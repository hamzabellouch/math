import Mathlib.Probability.Kernel.Composition.CompProd
import OAI.NumberTheory.Jacobsthal.Analysis.WeightIntegrals
import OAI.NumberTheory.Jacobsthal.Sieve.CompactExponentialMoments

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.KernelDensityBridge

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open DerivativeWeights TransitionKernels FinitePathGeometry FinitePathMeasures

theorem evenToOdd_map_ratio (s : EvenState) :
    (evenToOdd s).map (Subtype.val : OddState → ℝ) = evenKernel s := by
  calc
    _ = (evenKernel s).restrict (Ici (95 / 100 : ℝ)) := by
      change ((evenKernel s).comap (Subtype.val : OddState → ℝ)).map Subtype.val = _
      exact map_comap_subtype_coe (μ := evenKernel s) (s := Ici (95 / 100 : ℝ)) measurableSet_Ici
    _ = _ := Measure.restrict_eq_self_of_ae_mem (evenKernel_ae_odd_domain s)

theorem oddToEven_map_ratio (s : OddState) :
    (oddToEven s).map (Subtype.val : EvenState → ℝ) = oddKernel s := by
  calc
    _ = (oddKernel s).restrict (Ici (198 / 100 : ℝ)) := by
      change ((oddKernel s).comap (Subtype.val : EvenState → ℝ)).map Subtype.val = _
      exact map_comap_subtype_coe (μ := oddKernel s) (s := Ici (198 / 100 : ℝ)) measurableSet_Ici
    _ = _ := Measure.restrict_eq_self_of_ae_mem (oddKernel_ae_even_domain s)

theorem stateKernel_even_ratio (s : EvenState) :
    (stateKernel (.inl s)).map stateRatio = evenKernel s := by
  change (evenBranch s).map stateRatio = _
  rw [evenBranch, Kernel.map_apply _ measurable_inr,
    Measure.map_map stateRatio_measurable measurable_inr]
  exact evenToOdd_map_ratio s

theorem stateKernel_odd_ratio (s : OddState) :
    (stateKernel (.inr s)).map stateRatio = oddKernel s := by
  change (oddBranch s).map stateRatio = _
  rw [oddBranch, Kernel.map_apply _ measurable_inl,
    Measure.map_map stateRatio_measurable measurable_inl]
  exact oddToEven_map_ratio s

theorem evenToOdd_lintegral_ratio (s : EvenState) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ t : OddState, H t.1 ∂evenToOdd s) = ∫⁻ t, H t ∂evenKernel s := by
  rw [← evenToOdd_map_ratio, lintegral_map hH measurable_subtype_coe]

theorem oddToEven_lintegral_ratio (s : OddState) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ t : EvenState, H t.1 ∂oddToEven s) = ∫⁻ t, H t ∂oddKernel s := by
  rw [← oddToEven_map_ratio, lintegral_map hH measurable_subtype_coe]

theorem evenKernel_lintegral_density (s : EvenState) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ t, H t ∂evenKernel s) =
      ∫⁻ t, ENNReal.ofReal (transitionDensity .even s.1 t) * H t := by
  exact Kernel.lintegral_withDensity (Kernel.const EvenState volume)
    (f := fun s t => ENNReal.ofReal (evenDensity s t))
    (ENNReal.measurable_ofReal.comp evenDensity_measurable) s hH

theorem oddKernel_lintegral_density (s : OddState) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ t, H t ∂oddKernel s) =
      ∫⁻ t, ENNReal.ofReal (transitionDensity .odd s.1 t) * H t := by
  exact Kernel.lintegral_withDensity (Kernel.const OddState volume)
    (f := fun s t => ENNReal.ofReal (oddDensity s t))
    (ENNReal.measurable_ofReal.comp oddDensity_measurable) s hH

theorem transitionDensity_joint_measurable (i : Side) :
    Measurable (Function.uncurry (transitionDensity i)) := by
  cases i with
  | even =>
    change Measurable (fun x : ℝ × ℝ =>
      if x.1 - 1 ≤ x.2 then W x.2 * phiOdd x.2 / phiEven x.1 else 0)
    apply Measurable.ite (measurableSet_le (measurable_fst.sub measurable_const) measurable_snd)
    · exact ((W_measurable.comp measurable_snd).mul
        (phiOdd_continuous.measurable.comp measurable_snd)).div (phiEven_measurable.comp measurable_fst)
    · exact measurable_const
  | odd =>
    change Measurable (fun x : ℝ × ℝ =>
      if max 2 (x.1 - 1) ≤ x.2 then W x.2 * phiEven x.2 / phiOdd x.1 else 0)
    apply Measurable.ite (measurableSet_le
      (measurable_const.max (measurable_fst.sub measurable_const)) measurable_snd)
    · exact ((W_measurable.comp measurable_snd).mul
        (phiEven_measurable.comp measurable_snd)).div (phiOdd_continuous.measurable.comp measurable_fst)
    · exact measurable_const

noncomputable def evenTwoStep : Kernel EvenState (ℝ × ℝ) :=
  (evenToOdd ⊗ₖ oddToEven.prodMkLeft EvenState).map (fun x : OddState × EvenState => (x.1.1, x.2.1))

noncomputable def oddTwoStep : Kernel OddState (ℝ × ℝ) :=
  (oddToEven ⊗ₖ evenToOdd.prodMkLeft OddState).map (fun x : EvenState × OddState => (x.1.1, x.2.1))

instance evenTwoStep_isMarkovKernel : IsMarkovKernel evenTwoStep :=
  Kernel.IsMarkovKernel.map _ ((measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd))

instance oddTwoStep_isMarkovKernel : IsMarkovKernel oddTwoStep :=
  Kernel.IsMarkovKernel.map _ ((measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd))

theorem evenTwoStep_lintegral (s : EvenState) {H : ℝ × ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ x, H x ∂evenTwoStep s) = ∫⁻ t, ∫⁻ u,
      ENNReal.ofReal (transitionDensity .even s.1 t) *
        ENNReal.ofReal (transitionDensity .odd t u) * H (t, u) := by
  have hm : Measurable (fun x : OddState × EvenState => (x.1.1, x.2.1)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  rw [evenTwoStep, Kernel.lintegral_map _ hm _ hH]
  rw [Kernel.lintegral_compProd evenToOdd (oddToEven.prodMkLeft EvenState) s
    (f := fun x : OddState × EvenState => H (x.1.1, x.2.1)) (hH.comp hm)]
  change (∫⁻ t : OddState, ∫⁻ u : EvenState, H (t.1, u.1) ∂oddToEven t ∂evenToOdd s) = _
  have hinner : ∀ t : OddState, (∫⁻ u : EvenState, H (t.1, u.1) ∂oddToEven t) =
      ∫⁻ u, ENNReal.ofReal (transitionDensity .odd t.1 u) * H (t.1, u) := by
    intro t
    rw [oddToEven_lintegral_ratio t (H := fun u : ℝ => H (t.1, u)) (hH.comp measurable_prodMk_left),
      oddKernel_lintegral_density t (H := fun u : ℝ => H (t.1, u)) (hH.comp measurable_prodMk_left)]
  simp_rw [hinner]
  have hJ : Measurable (fun t : ℝ => ∫⁻ u,
      ENNReal.ofReal (transitionDensity .odd t u) * H (t, u)) :=
    ((ENNReal.measurable_ofReal.comp (transitionDensity_joint_measurable .odd)).mul hH).lintegral_prod_right
  rw [evenToOdd_lintegral_ratio s hJ, evenKernel_lintegral_density s hJ]
  apply lintegral_congr
  intro t
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro u
  ring

theorem oddTwoStep_lintegral (s : OddState) {H : ℝ × ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ x, H x ∂oddTwoStep s) = ∫⁻ t, ∫⁻ u,
      ENNReal.ofReal (transitionDensity .odd s.1 t) *
        ENNReal.ofReal (transitionDensity .even t u) * H (t, u) := by
  have hm : Measurable (fun x : EvenState × OddState => (x.1.1, x.2.1)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  rw [oddTwoStep, Kernel.lintegral_map _ hm _ hH]
  rw [Kernel.lintegral_compProd oddToEven (evenToOdd.prodMkLeft OddState) s
    (f := fun x : EvenState × OddState => H (x.1.1, x.2.1)) (hH.comp hm)]
  change (∫⁻ t : EvenState, ∫⁻ u : OddState, H (t.1, u.1) ∂evenToOdd t ∂oddToEven s) = _
  have hinner : ∀ t : EvenState, (∫⁻ u : OddState, H (t.1, u.1) ∂evenToOdd t) =
      ∫⁻ u, ENNReal.ofReal (transitionDensity .even t.1 u) * H (t.1, u) := by
    intro t
    rw [evenToOdd_lintegral_ratio t (H := fun u : ℝ => H (t.1, u)) (hH.comp measurable_prodMk_left),
      evenKernel_lintegral_density t (H := fun u : ℝ => H (t.1, u)) (hH.comp measurable_prodMk_left)]
  simp_rw [hinner]
  have hJ : Measurable (fun t : ℝ => ∫⁻ u,
      ENNReal.ofReal (transitionDensity .even t u) * H (t, u)) :=
    ((ENNReal.measurable_ofReal.comp (transitionDensity_joint_measurable .even)).mul hH).lintegral_prod_right
  rw [oddToEven_lintegral_ratio s hJ, oddKernel_lintegral_density s hJ]
  apply lintegral_congr
  intro t
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro u
  ring

noncomputable def jointDensity (i : Side) (s : ℝ) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (transitionDensity i s x.1) * ENNReal.ofReal (transitionDensity i.flip x.1 x.2)

theorem jointDensity_measurable (i : Side) (s : ℝ) : Measurable (jointDensity i s) := by
  exact (ENNReal.measurable_ofReal.comp ((transitionDensity_joint_measurable i).comp
    (measurable_const.prodMk measurable_fst))).mul
    (ENNReal.measurable_ofReal.comp (transitionDensity_joint_measurable i.flip))

theorem evenTwoStep_eq_withDensity (s : EvenState) :
    evenTwoStep s = ((volume : Measure ℝ).prod volume).withDensity (jointDensity .even s.1) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [evenTwoStep_lintegral s hH,
    lintegral_withDensity_eq_lintegral_mul _ (jointDensity_measurable .even s.1) hH]
  have hp := lintegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x => jointDensity .even s.1 x * H x) ((jointDensity_measurable .even s.1).mul hH).aemeasurable
  exact hp.symm

theorem oddTwoStep_eq_withDensity (s : OddState) :
    oddTwoStep s = ((volume : Measure ℝ).prod volume).withDensity (jointDensity .odd s.1) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [oddTwoStep_lintegral s hH,
    lintegral_withDensity_eq_lintegral_mul _ (jointDensity_measurable .odd s.1) hH]
  have hp := lintegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x => jointDensity .odd s.1 x * H x) ((jointDensity_measurable .odd s.1).mul hH).aemeasurable
  exact hp.symm

end NumberTheoryLean.KernelDensityBridge

end

section

namespace NumberTheoryLean.JointMinorization

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open DerivativeWeights TransitionKernels FinitePathGeometry FinitePathMeasures
open KernelDensityBridge TwoStepDensityBounds

def rectangle (L : ℝ) : Set (ℝ × ℝ) := Icc L (L + 1) ×ˢ Icc (L + 1) (L + 2)

theorem rectangle_measurable (L : ℝ) : MeasurableSet (rectangle L) :=
  measurableSet_Icc.prod measurableSet_Icc

noncomputable def rectangleLaw (L : ℝ) : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).prod volume).restrict (rectangle L)

instance rectangleLaw_isProbabilityMeasure (L : ℝ) : IsProbabilityMeasure (rectangleLaw L) := by
  constructor
  rw [rectangleLaw, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    rectangle, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  rw [show L + 1 - L = 1 by ring, show L + 2 - (L + 1) = 1 by ring]
  norm_num

theorem transitionDensity_nonneg {i : Side} {s : ℝ} (hs : Valid i s) (t : ℝ) :
    0 ≤ transitionDensity i s t := by
  cases i with
  | even => exact evenDensity_nonneg ⟨s, hs⟩ t
  | odd => exact oddDensity_nonneg ⟨s, hs⟩ t

theorem rectangle_minorization {i : Side} {s L : ℝ} (hL : 3 ≤ L)
    (hs : Valid i s) (hsL : s ≤ L) :
    ENNReal.ofReal (minorizationSize L) • rectangleLaw L ≤
      ((volume : Measure ℝ).prod volume).withDensity (jointDensity i s) := by
  rw [rectangleLaw, ← withDensity_const,
    ← withDensity_indicator (rectangle_measurable L)]
  apply withDensity_mono
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ rectangle L
  · rw [indicator_of_mem hx]
    change ENNReal.ofReal (minorizationSize L) ≤
      ENNReal.ofReal (transitionDensity i s x.1) * ENNReal.ofReal (transitionDensity i.flip x.1 x.2)
    rw [← ENNReal.ofReal_mul (transitionDensity_nonneg hs x.1)]
    exact ENNReal.ofReal_le_ofReal (le_trans (minorizationSize_le_rectangle i L)
      (rectangle_density_lower hL hs hsL hx.1 hx.2))
  · rw [indicator_of_notMem hx]
    exact zero_le

theorem evenTwoStep_rectangle_minorization {L : ℝ} (hL : 3 ≤ L)
    (s : EvenState) (hs : s.1 ≤ L) :
    ENNReal.ofReal (minorizationSize L) • rectangleLaw L ≤ evenTwoStep s := by
  rw [evenTwoStep_eq_withDensity]
  exact rectangle_minorization hL s.2 hs

theorem oddTwoStep_rectangle_minorization {L : ℝ} (hL : 3 ≤ L)
    (s : OddState) (hs : s.1 ≤ L) :
    ENNReal.ofReal (minorizationSize L) • rectangleLaw L ≤ oddTwoStep s := by
  rw [oddTwoStep_eq_withDensity]
  exact rectangle_minorization hL s.2 hs

noncomputable def pairCost (T : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.2, T + cost x.1 + cost x.2)

theorem pairCost_measurable (T : ℝ) : Measurable (pairCost T) :=
  measurable_snd.prodMk ((measurable_const.add (cost_measurable.comp measurable_fst)).add
    (cost_measurable.comp measurable_snd))

noncomputable def minorizingLaw (L T : ℝ) : Measure (ℝ × ℝ) := (rectangleLaw L).map (pairCost T)

instance minorizingLaw_isProbabilityMeasure (L T : ℝ) : IsProbabilityMeasure (minorizingLaw L T) :=
  (Measure.isProbabilityMeasure_map_iff (μ := rectangleLaw L)
    (pairCost_measurable T).aemeasurable).mpr inferInstance

noncomputable def evenJointKernel (T : ℝ) : Kernel EvenState (ℝ × ℝ) := evenTwoStep.map (pairCost T)
noncomputable def oddJointKernel (T : ℝ) : Kernel OddState (ℝ × ℝ) := oddTwoStep.map (pairCost T)

instance evenJointKernel_isMarkovKernel (T : ℝ) : IsMarkovKernel (evenJointKernel T) :=
  Kernel.IsMarkovKernel.map _ (pairCost_measurable T)

instance oddJointKernel_isMarkovKernel (T : ℝ) : IsMarkovKernel (oddJointKernel T) :=
  Kernel.IsMarkovKernel.map _ (pairCost_measurable T)

theorem even_joint_minorization {L : ℝ} (hL : 3 ≤ L) (s : EvenState) (hs : s.1 ≤ L) (T : ℝ) :
    ENNReal.ofReal (minorizationSize L) • minorizingLaw L T ≤ evenJointKernel T s := by
  rw [evenJointKernel, Kernel.map_apply _ (pairCost_measurable T)]
  have h := Measure.map_mono (evenTwoStep_rectangle_minorization hL s hs) (pairCost_measurable T)
  rw [Measure.map_smul _ (pairCost_measurable T).aemeasurable] at h
  exact h

theorem odd_joint_minorization {L : ℝ} (hL : 3 ≤ L) (s : OddState) (hs : s.1 ≤ L) (T : ℝ) :
    ENNReal.ofReal (minorizationSize L) • minorizingLaw L T ≤ oddJointKernel T s := by
  rw [oddJointKernel, Kernel.map_apply _ (pairCost_measurable T)]
  have h := Measure.map_mono (oddTwoStep_rectangle_minorization hL s hs) (pairCost_measurable T)
  rw [Measure.map_smul _ (pairCost_measurable T).aemeasurable] at h
  exact h

theorem compact_joint_minorization (S : ℝ) : ∃ L ε : ℝ, 3 ≤ L ∧ S ≤ L ∧ 0 < ε ∧ ε ≤ 1 ∧
    (∀ T : ℝ, IsProbabilityMeasure (minorizingLaw L T)) ∧
    (∀ T : ℝ, ∀ s : EvenState, s.1 ≤ S → ENNReal.ofReal ε • minorizingLaw L T ≤ evenJointKernel T s) ∧
    (∀ T : ℝ, ∀ s : OddState, s.1 ≤ S → ENNReal.ofReal ε • minorizingLaw L T ≤ oddJointKernel T s) := by
  refine ⟨max 3 S, minorizationSize (max 3 S), le_max_left _ _, le_max_right _ _,
    minorizationSize_pos (le_max_left _ _), minorizationSize_le_one _, ?_, ?_, ?_⟩
  · intro T
    infer_instance
  · intro T s hs
    exact even_joint_minorization (le_max_left _ _) s (le_trans hs (le_max_right _ _)) T
  · intro T s hs
    exact odd_joint_minorization (le_max_left _ _) s (le_trans hs (le_max_right _ _)) T

end NumberTheoryLean.JointMinorization

end

section

namespace NumberTheoryLean.GoodPairTransitions

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open BuchstabBridge DerivativeWeights WeightFutureIntegrals TransitionKernels
open FinitePathGeometry FinitePathMeasures KernelDensityBridge TwoStepDensityBounds JointMinorization

def goodPair (s : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc (max 2 (s - 1)) (max 2 (s - 1) + 1 / 4) ∧
    x.2 ∈ Icc (x.1 - 1) (x.1 - 3 / 4)}

theorem goodPair_measurable (s : ℝ) : MeasurableSet (goodPair s) := by
  exact ((measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    ((measurableSet_le (measurable_fst.sub measurable_const) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.sub measurable_const)))

theorem goodPair_volume (s : ℝ) : ((volume : Measure ℝ).prod volume) (goodPair s) = ENNReal.ofReal (1 / 16 : ℝ) := by
  rw [Measure.prod_apply (goodPair_measurable s)]
  have heq : ∀ t : ℝ, volume (Prod.mk t ⁻¹' goodPair s) =
      (Icc (max 2 (s - 1)) (max 2 (s - 1) + 1 / 4)).indicator
        (fun _ => ENNReal.ofReal (1 / 4 : ℝ)) t := by
    intro t
    by_cases ht : t ∈ Icc (max 2 (s - 1)) (max 2 (s - 1) + 1 / 4)
    · have hp : Prod.mk t ⁻¹' goodPair s = Icc (t - 1) (t - 3 / 4) := by
        ext u
        simp only [mem_preimage, goodPair, mem_ofPred_eq, ht, true_and]
      rw [hp, Real.volume_Icc, indicator_of_mem ht]
      congr 1
      ring
    · have hp : Prod.mk t ⁻¹' goodPair s = ∅ := by
        ext u
        simp only [mem_preimage, goodPair, mem_ofPred_eq, ht, false_and, mem_empty_iff_false]
      rw [hp, measure_empty, indicator_of_notMem ht]
  rw [lintegral_congr heq, lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc]
  rw [show max 2 (s - 1) + 1 / 4 - max 2 (s - 1) = (1 : ℝ) / 4 by ring]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  congr 1
  norm_num

theorem goodPair_bounds {s M t u : ℝ} (hM : 4 ≤ M) (hs : s ≤ M) (hg : (t, u) ∈ goodPair s) :
    2 ≤ t ∧ 1 ≤ u ∧ t ≤ M ∧ u ≤ M := by
  have ht2 : 2 ≤ t := le_trans (le_max_left _ _) hg.1.1
  have ha : max 2 (s - 1) ≤ M - 1 := max_le (by linarith) (by linarith)
  exact ⟨ht2, by linarith [hg.2.1], by linarith [hg.1.2], by linarith [hg.1.2, hg.2.2]⟩

theorem goodPair_terminal {s t u : ℝ} (hg : (t, u) ∈ goodPair s) :
    u ≤ max (3 / 2) (s - 3 / 2) := by
  by_cases hs : s ≤ 3
  · have ha : max 2 (s - 1) = 2 := max_eq_left (by linarith)
    have ht := hg.1.2
    rw [ha] at ht
    exact le_trans (show u ≤ 3 / 2 by linarith [hg.2.2]) (le_max_left _ _)
  · have ha : max 2 (s - 1) = s - 1 := max_eq_right (by linarith)
    have ht := hg.1.2
    rw [ha] at ht
    exact le_trans (show u ≤ s - 3 / 2 by linarith [hg.2.2]) (le_max_right _ _)

theorem phiOdd_le_A (s : ℝ) : phiOdd s ≤ sieveA := by
  by_cases hs : s ≤ 3
  · exact le_of_eq (phiOdd_initial hs)
  · have h := phiOdd_antitone (show 3 ≤ s by linarith)
    rwa [phiOdd_initial (s := 3) le_rfl] at h

noncomputable def goodPairDensityLower (M : ℝ) : ℝ := (1 / M) ^ 2 * (phiOdd M / sieveA)

theorem goodPairDensityLower_pos {M : ℝ} (hM : 4 ≤ M) : 0 < goodPairDensityLower M := by
  unfold goodPairDensityLower
  exact mul_pos (sq_pos_of_pos (one_div_pos.mpr (by linarith))) (div_pos (phiOdd_pos M) sieveA_pos)

theorem goodPair_density_lower {M : ℝ} (hM : 4 ≤ M) (s : OddState) (hs : s.1 ≤ M)
    {t u : ℝ} (hg : (t, u) ∈ goodPair s.1) :
    goodPairDensityLower M ≤ transitionDensity .odd s.1 t * transitionDensity .even t u := by
  obtain ⟨ht2, hu1, htM, huM⟩ := goodPair_bounds hM hs hg
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  have heq := two_step_density_eq (i := .odd) s.2 hg.1.1 hg.2.1
  change transitionDensity .odd s.1 t * transitionDensity .even t u =
    (W t * W u) * (phiOdd u / phiOdd s.1) at heq
  rw [heq]
  have hW : (1 / M) ^ 2 ≤ W t * W u := by
    simpa only [pow_two] using mul_le_mul (W_lower ht0 htM) (W_lower hu0 huM)
      (one_div_nonneg.mpr (by linarith)) (W_pos ht0).le
  have hr : phiOdd M / sieveA ≤ phiOdd u / phiOdd s.1 := by
    calc
      _ ≤ phiOdd M / phiOdd s.1 := div_le_div_of_nonneg_left (phiOdd_pos M).le (phiOdd_pos s.1) (phiOdd_le_A s.1)
      _ ≤ _ := div_le_div_of_nonneg_right (phiOdd_antitone huM) (phiOdd_pos s.1).le
  exact mul_le_mul hW hr (div_pos (phiOdd_pos M) sieveA_pos).le (mul_pos (W_pos ht0) (W_pos hu0)).le

theorem goodPair_measure_lower {M : ℝ} (hM : 4 ≤ M) (s : OddState) (hs : s.1 ≤ M) :
    ENNReal.ofReal (goodPairDensityLower M / 16) ≤ oddTwoStep s (goodPair s.1) := by
  have hdom : ENNReal.ofReal (goodPairDensityLower M) •
      ((volume : Measure ℝ).prod volume).restrict (goodPair s.1) ≤ oddTwoStep s := by
    rw [oddTwoStep_eq_withDensity, ← withDensity_const,
      ← withDensity_indicator (goodPair_measurable s.1)]
    apply withDensity_mono
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ goodPair s.1
    · rw [indicator_of_mem hx]
      change ENNReal.ofReal (goodPairDensityLower M) ≤
        ENNReal.ofReal (transitionDensity .odd s.1 x.1) * ENNReal.ofReal (transitionDensity .even x.1 x.2)
      rw [← ENNReal.ofReal_mul (transitionDensity_nonneg (i := .odd) s.2 x.1)]
      exact ENNReal.ofReal_le_ofReal (goodPair_density_lower hM s hs hx)
    · rw [indicator_of_notMem hx]
      exact zero_le
  have h := hdom (goodPair s.1)
  rw [Measure.smul_apply, Measure.restrict_apply (goodPair_measurable s.1), inter_self,
    goodPair_volume, smul_eq_mul, ← ENNReal.ofReal_mul (goodPairDensityLower_pos hM).le] at h
  convert! h using 1
  congr 1
  ring

noncomputable def goodPairProbability (M : ℝ) : ℝ := min (1 / 2) (goodPairDensityLower M / 16)

theorem goodPairProbability_pos {M : ℝ} (hM : 4 ≤ M) : 0 < goodPairProbability M :=
  lt_min (by norm_num) (div_pos (goodPairDensityLower_pos hM) (by norm_num))

theorem goodPairProbability_le_one (M : ℝ) : goodPairProbability M ≤ 1 :=
  le_trans (min_le_left _ _) (by norm_num)

theorem odd_terminal_progress {M : ℝ} (hM : 4 ≤ M) (s : OddState) (hs : s.1 ≤ M) :
    ENNReal.ofReal (goodPairProbability M) ≤
      oddTwoStep s {x : ℝ × ℝ | x.2 ≤ max (3 / 2) (s.1 - 3 / 2)} := by
  calc
    _ ≤ ENNReal.ofReal (goodPairDensityLower M / 16) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ ≤ oddTwoStep s (goodPair s.1) := goodPair_measure_lower hM s hs
    _ ≤ _ := measure_mono (fun x hx => goodPair_terminal hx)

end NumberTheoryLean.GoodPairTransitions

end

section

namespace NumberTheoryLean.FirstHitKernels

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open FinitePathMeasures

def regenerationStateSet : Set State :=
  fun z => Sum.elim (fun _ : TransitionKernels.EvenState => False)
    (fun s : TransitionKernels.OddState => s.1 ≤ 3) z

theorem regenerationStateSet_measurable : MeasurableSet regenerationStateSet := by
  apply measurableSet_sum_iff.mpr
  constructor
  · exact MeasurableSet.empty
  · exact measurableSet_le measurable_subtype_coe measurable_const

def regenerationSet : Set CostState := Prod.fst ⁻¹' regenerationStateSet

theorem regenerationSet_measurable : MeasurableSet regenerationSet :=
  regenerationStateSet_measurable.preimage measurable_fst

@[simp] theorem regeneration_even (s : TransitionKernels.EvenState) (T : ℝ) :
    (.inl s, T) ∉ regenerationSet := by change ¬False; exact not_false

@[simp] theorem regeneration_odd (s : TransitionKernels.OddState) (T : ℝ) :
    (.inr s, T) ∈ regenerationSet ↔ s.1 ≤ 3 := Iff.rfl

noncomputable def killed : Kernel CostState CostState := costKernel.restrict regenerationSet_measurable.compl
noncomputable def captured : Kernel CostState CostState := costKernel.restrict regenerationSet_measurable

instance killed_isFiniteKernel : IsFiniteKernel killed := by unfold killed; infer_instance
instance captured_isFiniteKernel : IsFiniteKernel captured := by unfold captured; infer_instance

instance killed_pow_isFiniteKernel (n : ℕ) : IsFiniteKernel (killed ^ n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel CostState CostState); infer_instance
  | succ n ih =>
    rw [pow_succ']
    change IsFiniteKernel (killed ∘ₖ (killed ^ n))
    infer_instance

theorem captured_add_killed : captured + killed = costKernel := by
  ext z : 1
  change (costKernel z).restrict regenerationSet + (costKernel z).restrict regenerationSetᶜ = costKernel z
  exact Measure.restrict_add_restrict_compl regenerationSet_measurable

noncomputable def firstHit (n : ℕ) : Kernel CostState CostState := captured ∘ₖ (killed ^ n)

instance firstHit_isFiniteKernel (n : ℕ) : IsFiniteKernel (firstHit n) := by
  unfold firstHit
  infer_instance

noncomputable def firstHitLaw : Kernel CostState CostState := Kernel.sum firstHit

instance firstHitLaw_isSFiniteKernel : IsSFiniteKernel firstHitLaw := by
  unfold firstHitLaw
  infer_instance

theorem firstHit_mass_step (n : ℕ) (z : CostState) :
    firstHit n z univ + (killed ^ (n + 1)) z univ = (killed ^ n) z univ := by
  have hp : killed ^ (n + 1) = killed ∘ₖ (killed ^ n) := pow_succ' killed n
  calc
    _ = ((captured + killed) ∘ₖ (killed ^ n)) z univ := by
      rw [Kernel.comp_add_left, add_apply, Measure.add_apply, hp]
      rfl
    _ = (costKernel ∘ₖ (killed ^ n)) z univ := by rw [captured_add_killed]
    _ = _ := by rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]; simp

theorem firstHit_finite_mass (n : ℕ) (z : CostState) :
    (killed ^ n) z univ + ∑ k ∈ Finset.range n, firstHit k z univ = 1 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, pow_zero]
    change (Measure.dirac z) univ = 1
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ = (∑ k ∈ Finset.range n, firstHit k z univ) +
          (firstHit n z univ + (killed ^ (n + 1)) z univ) := by ac_rfl
      _ = (∑ k ∈ Finset.range n, firstHit k z univ) + (killed ^ n) z univ := by rw [firstHit_mass_step]
      _ = 1 := by simpa only [add_comm] using ih

theorem survival_mass_le_one (n : ℕ) (z : CostState) : (killed ^ n) z univ ≤ 1 := by
  calc
    _ ≤ (killed ^ n) z univ + ∑ k ∈ Finset.range n, firstHit k z univ := le_add_of_nonneg_right zero_le
    _ = 1 := firstHit_finite_mass n z

theorem firstHit_partial_mass_le_one (n : ℕ) (z : CostState) :
    (∑ k ∈ Finset.range n, firstHit k z univ) ≤ 1 := by
  calc
    _ ≤ (killed ^ n) z univ + ∑ k ∈ Finset.range n, firstHit k z univ := le_add_of_nonneg_left zero_le
    _ = 1 := firstHit_finite_mass n z

theorem survival_mass_antitone (z : CostState) : Antitone (fun n => (killed ^ n) z univ) := by
  apply antitone_nat_of_succ_le
  intro n
  calc
    _ ≤ firstHit n z univ + (killed ^ (n + 1)) z univ := le_add_of_nonneg_left zero_le
    _ = _ := firstHit_mass_step n z

theorem firstHitLaw_mass_le_one (z : CostState) : firstHitLaw z univ ≤ 1 := by
  rw [firstHitLaw, Kernel.sum_apply' _ _ MeasurableSet.univ, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le (fun n => firstHit_partial_mass_le_one n z)

instance firstHitLaw_isFiniteKernel : IsFiniteKernel firstHitLaw :=
  ⟨1, by norm_num, fun z => firstHitLaw_mass_le_one z⟩

theorem firstHitLaw_probability_of_survival_vanishes (z : CostState)
    (hz : Tendsto (fun n => (killed ^ n) z univ) atTop (𝓝 0)) :
    IsProbabilityMeasure (firstHitLaw z) := by
  constructor
  rw [firstHitLaw, Kernel.sum_apply' _ _ MeasurableSet.univ]
  have hs := hz.add (ENNReal.tendsto_nat_tsum (fun n => firstHit n z univ))
  simp only [zero_add, firstHit_finite_mass] at hs
  exact tendsto_nhds_unique hs tendsto_const_nhds

theorem captured_off_regeneration (z : CostState) : captured z regenerationSetᶜ = 0 := by
  rw [captured, Kernel.restrict_apply' _ _ _ regenerationSet_measurable.compl,
    compl_inter_self, measure_empty]

theorem firstHit_off_regeneration (n : ℕ) (z : CostState) : firstHit n z regenerationSetᶜ = 0 := by
  rw [firstHit, Kernel.comp_apply' _ _ _ regenerationSet_measurable.compl]
  simp only [captured_off_regeneration, lintegral_zero]

theorem firstHitLaw_off_regeneration (z : CostState) : firstHitLaw z regenerationSetᶜ = 0 := by
  rw [firstHitLaw, Kernel.sum_apply' _ _ regenerationSet_measurable.compl]
  simp only [firstHit_off_regeneration, tsum_zero]

theorem costKernel_increases_cost (z : CostState) :
    costKernel z {y : CostState | y.2 ≤ z.2} = 0 := by
  rw [costKernel_apply z (measurableSet_le measurable_snd measurable_const)]
  have he : {s : State | ((s, z.2 + FinitePathGeometry.cost (stateRatio s)) : CostState).2 ≤ z.2} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hp := FinitePathGeometry.cost_pos (FinitePathGeometry.valid_pos (stateRatio_valid s))
    change z.2 + FinitePathGeometry.cost (stateRatio s) ≤ z.2 at hs
    linarith
  change (stateKernel z.1) {s : State | z.2 + FinitePathGeometry.cost (stateRatio s) ≤ z.2} = 0
  rw [he, measure_empty]

end NumberTheoryLean.FirstHitKernels

end

end Erdos970

end OAI
