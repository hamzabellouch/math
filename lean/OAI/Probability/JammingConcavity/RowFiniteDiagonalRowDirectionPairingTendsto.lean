import Mathlib
import OAI.Probability.JammingConcavity.RowFiniteDiagonal

namespace OAI

/-! Row Finite Diagonal Row Direction Pairing Tendsto. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open scoped BigOperators Classical
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder
open scoped BigOperators RealInnerProductSpace
open scoped NNReal Topology BigOperators
open scoped NNReal BigOperators RealInnerProductSpace
open scoped ENNReal NNReal BigOperators MatrixOrder
open scoped MatrixOrder
open scoped NNReal
open scoped BigOperators NNReal
open scoped NNReal ENNReal BigOperators Topology
open scoped Topology ENNReal NNReal
open scoped Matrix.Norms.L2Operator MatrixOrder Topology NNReal ENNReal BigOperators
open scoped Topology ENNReal NNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped Topology NNReal ENNReal BigOperators
open scoped BigOperators NNReal Topology
open scoped Topology NNReal ENNReal BigOperators MatrixOrder
open scoped Topology NNReal ENNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace MicroscopicJamming
 

def RowFiniteFTCStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
    ∀ bs : List (ℝ × ℝ × ℝ),
      (∀ c ∈ bs, 0 ≤ c.1 ∧ c.1 ≤ 1 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2) →
      bs.Pairwise (fun c d => c.1 ≤ d.1) → rowVarianceTotal bs=0 →
      ∀ x : ℝ,
        gaussianRowComposition (rowInterpolatedBlocks bs 1) u x-
          gaussianRowComposition (rowInterpolatedBlocks bs 0) u x =
        ∫ t in (0:ℝ)..1, -(1/2:ℝ)*(∫ s in (0:ℝ)..1,
          (gaussianRankProfile (bs.map (fun c => (c.1,c.2.2))) s-
           gaussianRankProfile (bs.map (fun c => (c.1,c.2.1))) s)*
           rowDerivativeRankMoment (rowInterpolatedBlocks bs t) u s x)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma rowBoundedFamily_composed_continuousAt {f : ℝ → ℝ → ℝ} {L H t₀ : ℝ}
    (hf : ∀ t, RowBoundedTerminal (f t) L H)
    (hc : ∀ y, ContinuousAt (fun t => f t y) t₀)
    {g : ℝ → ℝ} (hg : ContinuousAt g t₀) : ContinuousAt (fun t => f t (g t)) t₀ := by
  have hb (t : ℝ) : ‖f t (g t)-f t (g t₀)‖ ≤ L*‖g t-g t₀‖ := by
    exact Convex.norm_image_sub_le_of_norm_deriv_le (f := f t) (s := univ)
      (fun y _ => (hf t).diff y) (fun y _ => by simpa only [Real.norm_eq_abs] using (hf t).slope y)
      convex_univ (mem_univ _) (mem_univ _)
  have ht : Tendsto (fun t => f t (g t)-f t (g t₀)) (𝓝 t₀) (𝓝 0) := by
    apply squeeze_zero_norm hb
    simpa only [sub_self,norm_zero,mul_zero] using
      (tendsto_const_nhds.mul ((hg.tendsto.sub tendsto_const_nhds).norm) :
        Tendsto (fun t => L*‖g t-g t₀‖) (𝓝 t₀) (𝓝 (L*‖g t₀-g t₀‖)))
  have hh := ht.add (hc (g t₀)).tendsto
  change Tendsto (fun t => f t (g t)) (𝓝 t₀) (𝓝 (f t₀ (g t₀)))
  simpa only [sub_add_cancel,zero_add] using hh

lemma rowOperator_parameter_continuousAt {f : ℝ → ℝ → ℝ} {L H t₀ : ℝ}
    (hf : ∀ t, RowBoundedTerminal (f t) L H)
    (hc : ∀ y, ContinuousAt (fun t => f t y) t₀)
    {T : ℝ → ℝ} (hT : ContinuousAt T t₀) (a x : ℝ) :
    ContinuousAt (fun t => gaussianRowOperator a (T t) (f t) x) t₀ := by
  let A := |f t₀ 0|+1
  let B := |Real.sqrt (T t₀)|+1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL := (hf t₀).L_nonneg
  have heA : ∀ᶠ t in 𝓝 t₀, |f t 0| ≤ A := by
    exact ((hc 0).abs.eventually_lt continuousAt_const (by dsimp [A]; linarith)).mono (fun _ h => h.le)
  have heB : ∀ᶠ t in 𝓝 t₀, |Real.sqrt (T t)| ≤ B := by
    exact ((Real.continuous_sqrt.continuousAt.comp hT).abs.eventually_lt continuousAt_const
      (by dsimp [B]; linarith)).mono (fun _ h => h.le)
  have hlinear : ∀ᶠ t in 𝓝 t₀, ∀ z : ℝ, |f t (x+Real.sqrt (T t)*z)| ≤ A+L*|x|+(L*B)*|z| := by
    filter_upwards [heA,heB] with t ha hb
    intro z
    have h := bounded_deriv_linear (hf t).diff (hf t).slope (x+Real.sqrt (T t)*z)
    have hg : |x+Real.sqrt (T t)*z| ≤ |x|+B*|z| := by
      calc
        _ ≤ |x|+|Real.sqrt (T t)*z| := abs_add_le _ _
        _ ≤ _ := by rw [abs_mul]; gcongr
    nlinarith [mul_le_mul_of_nonneg_left hg hL]
  have hcomp (z : ℝ) : ContinuousAt (fun t => f t (x+Real.sqrt (T t)*z)) t₀ :=
    rowBoundedFamily_composed_continuousAt hf hc (continuousAt_const.add ((Real.continuous_sqrt.continuousAt.comp hT).mul_const z))
  by_cases ha : a=0
  · subst a
    simp only [gaussianRowOperator,gaussianHeat]
    let C := A+L*|x|+L*B
    have hC : 0 ≤ C := by dsimp [C]; positivity
    apply continuousAt_of_dominated (bound := fun z => C*Real.exp |z|)
      (Eventually.of_forall (fun t => ((hf t).diff.continuous.measurable.comp (by fun_prop)).aestronglyMeasurable)) ?_
      ((gaussian_exp_abs_integrable 1).const_mul C |>.congr (Eventually.of_forall (by intro z; simp)))
      (Eventually.of_forall hcomp)
    filter_upwards [hlinear] with t ht
    apply Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs]
    have h₁ : 1 ≤ Real.exp |z| := Real.one_le_exp (abs_nonneg z)
    have h₂ : |z| ≤ Real.exp |z| := by linarith [Real.add_one_le_exp |z|]
    apply (ht z).trans
    calc
      _ ≤ (A+L*|x|)*Real.exp |z|+(L*B)*Real.exp |z| :=
        add_le_add (le_mul_of_one_le_right (by positivity) h₁)
          (mul_le_mul_of_nonneg_left h₂ (mul_nonneg hL hB))
      _ = _ := by dsimp [C]; ring
  · have hci : ContinuousAt (fun t => ∫ z, Real.exp (a*f t (x+Real.sqrt (T t)*z)) ∂gaussianReal 0 1) t₀ := by
      apply continuousAt_of_dominated
        (bound := fun z => Real.exp (|a| *(A+L*|x|))*Real.exp ((|a| *L*B)*|z|))
        (Eventually.of_forall (fun t => (((hf t).diff.continuous.measurable.comp (by fun_prop)).const_mul a).exp.aestronglyMeasurable)) ?_
        ((gaussian_exp_abs_integrable (|a| *L*B)).const_mul (Real.exp (|a| *(A+L*|x|))))
        (Eventually.of_forall (fun z => Real.continuous_exp.continuousAt.comp ((hcomp z).const_mul a)))
      filter_upwards [hlinear] with t ht
      apply Eventually.of_forall
      intro z
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hb : a*f t (x+Real.sqrt (T t)*z) ≤ |a| *|f t (x+Real.sqrt (T t)*z)| := by
        simpa only [abs_mul] using le_abs_self (a*f t (x+Real.sqrt (T t)*z))
      dsimp only [Function.comp_def]
      calc
        _ ≤ |a| * |f t (x+Real.sqrt (T t)*z)| := hb
        _ ≤ |a| * (A+L*|x|+L*B*|z|) := mul_le_mul_of_nonneg_left (ht z) (abs_nonneg a)
        _ = _ := by ring
    have hp : (∫ z, Real.exp (a*f t₀ (x+Real.sqrt (T t₀)*z)) ∂gaussianReal 0 1) ≠ 0 :=
      (integral_exp_pos (rowTiltStep_weight_integrable (hf t₀).diff.continuous.measurable
        (rowBounded_exp_growth (hf t₀) a).1 (T t₀) x)).ne'
    simpa only [gaussianRowOperator,ite_eq_right ha,gaussianHeat] using (hci.log hp).const_mul (1/a)

lemma rowVarianceComposition_continuous {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (bs : List (ℝ × ℝ × ℝ)) (hbs : ∀ b ∈ bs, 0 ≤ b.1 ∧ b.1 ≤ 1) (x : ℝ) :
    Continuous (fun t => gaussianRowComposition (rowInterpolatedBlocks bs t) u x) := by
  induction bs generalizing x with
  | nil => exact continuous_const
  | cons b bs ih =>
    rcases b with ⟨a,T,R⟩
    have htail := fun c hc => hbs c (List.mem_cons_of_mem _ hc)
    obtain ⟨K,C,hC,hf,hm,hb⟩ := rowVarianceFamily_bounds hu bs htail
    apply continuous_iff_continuousAt.mpr
    intro t
    exact rowOperator_parameter_continuousAt hf (fun y => (ih htail y).continuousAt) (by fun_prop) a x
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace MicroscopicJamming

theorem rowFiniteFTC : RowFiniteFTCStatement := by
  intro u L H hu hL hH hb bs hbs hord htotal x
  have hbu := rowTerminal_of_C2 hu hL hH hb
  let F := fun t => gaussianRowComposition (rowInterpolatedBlocks bs t) u x
  let F' := fun t => -(1/2:ℝ)*(∫ s in (0:ℝ)..1,
    (gaussianRankProfile (bs.map (fun c => (c.1,c.2.2))) s-
      gaussianRankProfile (bs.map (fun c => (c.1,c.2.1))) s)*
      rowDerivativeRankMoment (rowInterpolatedBlocks bs t) u s x)
  have hd : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt F (F' t) t :=
    fun t ht => rowFiniteIntegral u L H hu hL hH hb bs hbs hord htotal t ht x
  obtain ⟨K,C,hC,hf,hm,hbound⟩ := rowVarianceFamily_bounds hbu bs (fun c hc => ⟨(hbs c hc).1,(hbs c hc).2.1⟩)
  have he : F' =ᵐ[volume.restrict (Set.Ioo (0:ℝ) 1)] deriv F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hd t ht).deriv.symm
  have hi : IntervalIntegrable F' volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply (integrable_const C).mono' ((aestronglyMeasurable_deriv F _).congr he.symm)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hv := rowFiniteVariance u L H hu hL hH hb bs hbs t ht x
    have heq : F' t = rowFiniteVarianceResponse bs u t x := (hd t ht).deriv.symm.trans hv.deriv
    rw [Real.norm_eq_abs,heq]
    exact hbound t x
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1)
    (rowVarianceComposition_continuous hbu bs (fun c hc => ⟨(hbs c hc).1,(hbs c hc).2.1⟩) x).continuousOn hd hi).symm
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace MicroscopicJamming
 

def RowFiniteProfile.functional {Q : ℝ} (P : RowFiniteProfile Q) (u : ℝ → ℝ) : ℝ :=
  gaussianRowComposition ((0,(P.root:ℝ))::(rowGaussianBlocks P.ranks P.increment ++ [(1,(P.residual:ℝ))])) u 0

 

def RowFiniteFunctionalStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
    ∀ Q : ℝ, ∀ P : RowFiniteProfile Q,
      (∫ ω, Real.log (replicaZ (rowReplicaKernel P.ranks P.residual) (rowFullPotential P.ranks u) ω)
        ∂rowReplicaEnvironmentLaw P.ranks P.increment P.root) = P.functional u
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace MicroscopicJamming
lemma gaussianRowComposition_append_eq (bs cs : List (ℝ × ℝ)) (u : ℝ → ℝ) :
    gaussianRowComposition (bs++cs) u = gaussianRowComposition bs (gaussianRowComposition cs u) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append,gaussianRowComposition,ih]

lemma integrable_cascade_coordinates {E : Type} [MeasurableSpace E] [AddCommMonoid E]
    [MeasurableAdd₂ E] (ms : List ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (ν : ℕ → Measure E) [∀ j, IsProbabilityMeasure (ν j)]
    {f : E × FamilyCascadeTree E ms.length → ℝ} (hf : Measurable f)
    {g : CascadeTree ms.length × (Option (CascadeMarkIndex ms.length) → E) → ℝ} (hg : Measurable g)
    (he : ∀ ω x y, f (x,zipCascade ms.length (ω,y)) = g (ω,rootMarkCoordinates ms.length (x,y))) :
    Integrable f (μ.prod (familyCascadeLaw ms.length ν)) ↔
      Integrable g ((cascadeLaw ms).prod (Measure.infinitePi
        (fun i : Option (CascadeMarkIndex ms.length) => i.elim μ (fun j => ν (cascadeMarkDepth ms.length j))))) := by
  rw [← zipRootCascade_law ms μ ν,
    integrable_map_measure hf.aestronglyMeasurable (measurable_zipRootCascade ms.length).aemeasurable]
  have hmap := rootMarkCoordinates_law ms.length μ ν
  rw [← hmap, ← (Measure.map_id (μ := cascadeLaw ms)),
    Measure.map_prod_map _ _ measurable_id (measurable_rootMarkCoordinates ms.length),
    integrable_map_measure hg.aestronglyMeasurable (measurable_id.prodMap (measurable_rootMarkCoordinates ms.length)).aemeasurable]
  rw [Measure.map_id]
  apply integrable_congr
  exact Eventually.of_forall fun z => he z.1 z.2.1 z.2.2

lemma replica_log_integrable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (G : Kernel Ω S) [IsMarkovKernel G]
    {V : Ω × S → ℝ} (hV : Measurable V)
    (h4 : Integrable (fun z => Real.exp (4*|V z|)) (ν ⊗ₘ G)) :
    Integrable (fun ω => Real.log (replicaZ G V ω)) ν := by
  have hsplit := (Measure.integrable_compProd_iff h4.aestronglyMeasurable).mp h4
  have hAi : Integrable (fun ω => ∫ x, Real.exp (4*|V (ω,x)|) ∂G ω) ν := by
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hsplit.2
  apply (hAi.const_mul 2).mono' (Real.measurable_log.comp (measurable_replicaZ G hV)).aestronglyMeasurable
  filter_upwards [hsplit.1] with ω hω
  simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq,replicaZ] using
    (replica_fiber_log_estimates (G ω) (hV.comp (measurable_const.prodMk measurable_id)) hω (le_refl (0:ℝ))).2.2.1

lemma rowResidual_partition_pointwise {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (ms : List ℝ) (Δ : ℝ≥0) (ω : RowReplicaEnvironment ms.length) :
    replicaZ (rowReplicaKernel ms Δ) (rowFullPotential ms u) ω =
      replicaZ (rowCoordinateLeafKernel ms) (rowCoordinatePotential ms (gaussianRowOperator 1 Δ u)) ω := by
  let := cascadeLeafLaw_probability ms ω.1
  exact residual_partition_eq (cascadeLeafLaw ms ω.1) (rootPathField ms.length ω.2)
    (measurable_of_countable _) hu Δ
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace MicroscopicJamming

theorem rowGaussianCascade : RowGaussianCascadeStatement := by
  intro u L H hu hL hH hb ms hord hms d Δ p₀
  let v := gaussianRowOperator 1 Δ u
  have ht := rowTerminal_of_C2 hu hL hH hb
  have hv := rowBoundedOperator_terminal ht (by norm_num : (0:ℝ)≤1) le_rfl (Δ:ℝ)
  obtain ⟨he,hf⟩ := rowGaussian_recursion hv ms hms d
  have he' (x : ℝ) : familyRecursion ms (rowGaussianLaw d) v x =
      gaussianRowComposition (rowGaussianBlocks ms d++[(1,(Δ:ℝ))]) u x := by
    rw [gaussianRowComposition_append_eq]
    exact congrFun he x
  have (k : ℕ) : IsProbabilityMeasure (rowGaussianLaw d k) := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 (d k)))
  have hg := familyCascadeLog ℝ inferInstance inferInstance inferInstance ms hord hms
    (rowGaussianLaw d) (fun _ => inferInstance) v hv.diff.continuous.measurable hf
  refine ⟨hf,he',fun x => (hg x).2.2.1,?_⟩
  change (∫ z, ∫ ω, familyLogPartition ms v z ω ∂familyCascadeLaw ms.length (rowGaussianLaw d) ∂gaussianReal 0 p₀) = _
  have hinner (z : ℝ) : (∫ ω, familyLogPartition ms v z ω ∂familyCascadeLaw ms.length (rowGaussianLaw d)) =
      gaussianRowComposition (rowGaussianBlocks ms d) v z := (hg z).2.2.2.trans (congrFun he z)
  simp_rw [hinner]
  obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hv (rowGaussianBlocks ms d)
    (rowGaussianBlocks_valid ms (fun a ha => ⟨(hms a ha).1.le,(hms a ha).2.le⟩) d)
  simp only [gaussianRowComposition]
  rw [gaussianRowComposition_append_eq]
  change (∫ z, gaussianRowComposition (rowGaussianBlocks ms d) v z ∂gaussianReal 0 p₀) =
    gaussianRowOperator 0 (p₀:ℝ) (gaussianRowComposition (rowGaussianBlocks ms d) v) 0
  rw [rowGaussian_integral p₀ hK.diff.continuous.measurable]
  simp [gaussianRowOperator,gaussianHeat]
  rfl
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace MicroscopicJamming

lemma rowFiniteFunctional_log_integrable {u : ℝ → ℝ} {L H : ℝ}
    (hu : RowBoundedTerminal u L H) {Q : ℝ} (P : RowFiniteProfile Q) :
    Integrable (fun ω => Real.log (replicaZ (rowReplicaKernel P.ranks P.residual)
      (rowFullPotential P.ranks u) ω)) (rowReplicaEnvironmentLaw P.ranks P.increment P.root) := by
  have : IsProbabilityMeasure (rowReplicaEnvironmentLaw P.ranks P.increment P.root) := by
    unfold rowReplicaEnvironmentLaw; infer_instance
  obtain ⟨C,hC⟩ := rowUniformMoments hu Q (fun _ => P) 4 (by norm_num)
  exact replica_log_integrable _ _ (measurable_rowFullPotential _ _ hu.diff.continuous.measurable) (hC 0).1

lemma familyCoordinate_log_expectation {u : ℝ → ℝ} {L H : ℝ}
    (hu : RowBoundedTerminal u L H) (ms : List ℝ) (hord : ms.Pairwise (· < ·))
    (hms : ∀ m ∈ ms, 0 < m ∧ m < 1) (d : ℕ → ℝ≥0) (x : ℝ) :
    (∫ ω, Real.log (replicaZ (familyCoordinateKernel ms) (familyCoordinatePotential ms u) (x,ω))
      ∂familyCascadeLaw ms.length (rowGaussianLaw d)) =
      gaussianRowComposition (rowGaussianBlocks ms d) u x := by
  have (k : ℕ) : IsProbabilityMeasure (rowGaussianLaw d k) := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 (d k)))
  obtain ⟨he,hf⟩ := rowGaussian_recursion hu ms hms d
  have hg := familyCascadeLog ℝ inferInstance inferInstance inferInstance ms hord hms
    (rowGaussianLaw d) (fun _ => inferInstance) u hu.diff.continuous.measurable hf x
  rw [← congrFun he x,← hg.2.2.2]
  apply integral_congr_ae
  filter_upwards [(familyUnmarkedTotal_properties ms hord hms (rowGaussianLaw d) (fun _ => inferInstance)).1] with ω hω
  change Real.log (∫ ℓ, Real.exp (u (familyPathMark ms.length x ω ℓ))
    ∂cascadeLeafLaw ms (forgetFamilyMarks ms.length ω)) = _
  rw [familyBaseLeaf_Z ms u x ω hω,ENNReal.toReal_div]
  simp only [familyLogPartition,familyLeafTotal_zero]

theorem rowFiniteFunctional : RowFiniteFunctionalStatement := by
  intro u L H hu hL hH hb Q P
  have ht := rowTerminal_of_C2 hu hL hH hb
  let v := gaussianRowOperator 1 P.residual u
  have hv := rowBoundedOperator_terminal ht (by norm_num : (0:ℝ)≤1) le_rfl (P.residual:ℝ)
  let f := fun z : ℝ × FamilyCascadeTree ℝ P.ranks.length =>
    Real.log (replicaZ (familyCoordinateKernel P.ranks) (familyCoordinatePotential P.ranks v) z)
  let g := fun ω : RowReplicaEnvironment P.ranks.length =>
    Real.log (replicaZ (rowCoordinateLeafKernel P.ranks) (rowCoordinatePotential P.ranks v) ω)
  have hf : Measurable f := Real.measurable_log.comp (measurable_replicaZ _ (measurable_familyCoordinatePotential _ hv.diff.continuous.measurable))
  have hg : Measurable g := Real.measurable_log.comp (measurable_replicaZ _ (measurable_rowCoordinatePotential _ hv.diff.continuous.measurable))
  have (k : ℕ) : IsProbabilityMeasure (rowGaussianLaw P.increment k) := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 (P.increment k)))
  let := familyCascadeLaw_probability P.ranks.length (rowGaussianLaw P.increment) (fun _ => inferInstance)
  have heq : ∀ ω x y, f (x,zipCascade P.ranks.length (ω,y)) = g (ω,rootMarkCoordinates P.ranks.length (x,y)) := by
    intro ω x y
    simp only [f,g,replicaZ,familyCoordinateKernel,Kernel.coe_mk,familyCoordinatePotential,
      rowCoordinateLeafKernel,rowCoordinatePotential,forgetFamilyMarks_zip,rootPathField_eq]
  have hlaw : (fun i : Option (CascadeMarkIndex P.ranks.length) => i.elim (gaussianReal 0 P.root)
        (fun j => rowGaussianLaw P.increment (cascadeMarkDepth P.ranks.length j))) =
      (fun i => gaussianReal 0 (rootCoordinateVariance P.ranks.length P.increment P.root i)) := by
    funext i
    cases i <;> rfl
  have hgi : Integrable g (rowReplicaEnvironmentLaw P.ranks P.increment P.root) := by
    apply (rowFiniteFunctional_log_integrable ht P).congr
    exact Eventually.of_forall (fun ω => congrArg Real.log (rowResidual_partition_pointwise ht P.ranks P.residual ω))
  have hfi : Integrable f ((gaussianReal 0 P.root).prod (familyCascadeLaw P.ranks.length (rowGaussianLaw P.increment))) := by
    apply (integrable_cascade_coordinates P.ranks (gaussianReal 0 P.root) (rowGaussianLaw P.increment) hf hg heq).mpr
    simpa only [hlaw,rowReplicaEnvironmentLaw] using hgi
  have he := integral_cascade_coordinates P.ranks (gaussianReal 0 P.root) (rowGaussianLaw P.increment) hf hg heq
  rw [hlaw] at he
  calc
    _ = ∫ ω, g ω ∂rowReplicaEnvironmentLaw P.ranks P.increment P.root := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => congrArg Real.log (rowResidual_partition_pointwise ht P.ranks P.residual ω))
    _ = ∫ z, f z ∂(gaussianReal 0 P.root).prod (familyCascadeLaw P.ranks.length (rowGaussianLaw P.increment)) := he.symm
    _ = ∫ x, gaussianRowComposition (rowGaussianBlocks P.ranks P.increment) v x ∂gaussianReal 0 P.root := by
      rw [integral_prod _ hfi]
      apply integral_congr_ae
      exact Eventually.of_forall (familyCoordinate_log_expectation hv P.ranks P.ordered P.valid P.increment)
    _ = P.functional u := by
      obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hv (rowGaussianBlocks P.ranks P.increment)
        (rowGaussianBlocks_valid P.ranks (fun a ha => ⟨(P.valid a ha).1.le,(P.valid a ha).2.le⟩) P.increment)
      rw [rowGaussian_integral P.root hK.diff.continuous.measurable]
      simp only [RowFiniteProfile.functional,gaussianRowComposition,gaussianRowOperator,gaussianHeat,zero_add]
      rw [gaussianRowComposition_append_eq]
      rfl
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace MicroscopicJamming
abbrev RowProfile (Q : ℝ) := {q : SphericalProfile // q.val 1 ≤ Q}
def rowUnitClip (t : ℝ) : ℝ := max 0 (min 1 t)
lemma rowUnitClip_mem (t : ℝ) : rowUnitClip t ∈ Set.Icc (0:ℝ) 1 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
lemma rowUnitClip_eq {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : rowUnitClip t=t := by
  simp [rowUnitClip,min_eq_right ht.2,max_eq_right ht.1]
 

def rowProfileMix {Q : ℝ} (q r : RowProfile Q) (t : ℝ) : RowProfile Q :=
  ⟨{val := fun s => (1-rowUnitClip t)*q.1.val s+rowUnitClip t*r.1.val s
    mono := by
      intro a ha b hb hab
      exact add_le_add (mul_le_mul_of_nonneg_left (q.1.mono ha hb hab) (sub_nonneg.mpr (rowUnitClip_mem t).2))
        (mul_le_mul_of_nonneg_left (r.1.mono ha hb hab) (rowUnitClip_mem t).1)
    nonneg := by
      intro s hs
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr (rowUnitClip_mem t).2) (q.1.nonneg s hs))
        (mul_nonneg (rowUnitClip_mem t).1 (r.1.nonneg s hs))},by
      have h1 := mul_le_mul_of_nonneg_left q.2 (sub_nonneg.mpr (rowUnitClip_mem t).2)
      have h2 := mul_le_mul_of_nonneg_left r.2 (rowUnitClip_mem t).1
      dsimp
      nlinarith⟩
 

def RowGeneralInterpolationStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ Q : ℝ, ∃ (Phi : RowProfile Q → ℝ) (D : RowProfile Q → SphericalProfile),
    (∀ q s, s ∈ Set.Icc 0 1 → (D q).val s ≤ L^2) ∧
    (∀ (q : RowProfile Q) (P : ℕ → RowFiniteProfile Q),
      Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.1.val) atTop (𝓝 0) →
      Tendsto (fun n => (P n).functional u) atTop (𝓝 (Phi q)) ∧
      Tendsto (fun n => sphericalProfileDistance ((P n).derivative u) (D q).val) atTop (𝓝 0)) ∧
    (∀ (q : RowProfile Q) (qn : ℕ → RowProfile Q),
      Tendsto (fun n => sphericalProfileDistance (qn n).1.val q.1.val) atTop (𝓝 0) →
      Tendsto (fun n => Phi (qn n)) atTop (𝓝 (Phi q)) ∧
      Tendsto (fun n => sphericalProfileDistance (D (qn n)).val (D q).val) atTop (𝓝 0)) ∧
    (∀ q r : RowProfile Q, ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt (fun v => Phi (rowProfileMix q r v))
        (-(1/2:ℝ)*(∫ s in (0:ℝ)..1, (r.1.val s-q.1.val s)*(D (rowProfileMix q r t)).val s))
        (Set.Icc (0:ℝ) 1) t) ∧
    (∀ q r : RowProfile Q, |Phi q-Phi r| ≤ (1/2:ℝ)*L^2*sphericalProfileDistance q.1.val r.1.val) ∧
    (∀ q : RowProfile Q, ∀ a b c : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      (∀ᵐ s ∂volume.restrict (Set.Ioo a b), q.1.val s=c) →
      ∃ d : ℝ, ∀ᵐ s ∂volume.restrict (Set.Ioo a b), (D q).val s=d)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma rowUnitClip_continuous : Continuous rowUnitClip := continuous_const.max (continuous_const.min continuous_id)
lemma rowProfileMix_zero {Q : ℝ} (q r : RowProfile Q) : rowProfileMix q r 0=q := by
  apply Subtype.ext
  apply sphericalProfile_ext
  funext s
  simp [rowProfileMix,rowUnitClip]
lemma rowProfileMix_one {Q : ℝ} (q r : RowProfile Q) : rowProfileMix q r 1=r := by
  apply Subtype.ext
  apply sphericalProfile_ext
  funext s
  simp [rowProfileMix,rowUnitClip]

lemma rowFiniteProfile_top_le {Q : ℝ} (P : RowFiniteProfile Q) : P.profile.val 1 ≤ Q := by
  have hs : P.profile.val 1 = (P.root:ℝ)+∑ j : Fin P.ranks.length, (P.increment j:ℝ) := by
    rw [RowFiniteProfile.profile,rowCascadeProfile_sum _ P.ordered,rowGaussianBlocks_cumulative]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : P.ranks[j.val]! ∈ P.ranks := by
      rw [getElem!_pos P.ranks j.val j.isLt]
      exact List.getElem_mem j.isLt
    rw [ite_eq_left (P.valid _ hjm).2.le]
  rw [hs]
  have hd := P.diagonal
  simp only [rowReplicaDiagonal,NNReal.coe_add,NNReal.coe_sum] at hd
  linarith [P.residual.coe_nonneg]

def RowFiniteProfile.asProfile {Q : ℝ} (P : RowFiniteProfile Q) : RowProfile Q := ⟨P.profile,rowFiniteProfile_top_le P⟩

lemma rowProfileMix_distance {Q : ℝ} (q r p v : RowProfile Q) (t : ℝ) :
    sphericalProfileDistance (rowProfileMix q r t).1.val (rowProfileMix p v t).1.val ≤
      (1-rowUnitClip t)*sphericalProfileDistance q.1.val p.1.val +
        rowUnitClip t*sphericalProfileDistance r.1.val v.1.val := by
  unfold sphericalProfileDistance
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ←intervalIntegral.integral_add ((q.1.integrable.sub p.1.integrable).abs.const_mul _)
      ((r.1.integrable.sub v.1.integrable).abs.const_mul _)]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((rowProfileMix q r t).1.integrable.sub (rowProfileMix p v t).1.integrable).abs
    (((q.1.integrable.sub p.1.integrable).abs.const_mul _).add ((r.1.integrable.sub v.1.integrable).abs.const_mul _))
  intro s hs
  change |(1-rowUnitClip t)*q.1.val s+rowUnitClip t*r.1.val s-
    ((1-rowUnitClip t)*p.1.val s+rowUnitClip t*v.1.val s)| ≤ _
  calc
    _ = |(1-rowUnitClip t)*(q.1.val s-p.1.val s)+rowUnitClip t*(r.1.val s-v.1.val s)| := by congr 1; ring
    _ ≤ |(1-rowUnitClip t)*(q.1.val s-p.1.val s)|+|rowUnitClip t*(r.1.val s-v.1.val s)| := abs_add_le _ _
    _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr (rowUnitClip_mem t).2),abs_of_nonneg (rowUnitClip_mem t).1]

lemma rowProfileMix_parameter_distance {Q : ℝ} (q r : RowProfile Q) (t v : ℝ) :
    sphericalProfileDistance (rowProfileMix q r t).1.val (rowProfileMix q r v).1.val =
      |rowUnitClip t-rowUnitClip v| *sphericalProfileDistance r.1.val q.1.val := by
  unfold sphericalProfileDistance
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  change |(1-rowUnitClip t)*q.1.val s+rowUnitClip t*r.1.val s-
    ((1-rowUnitClip v)*q.1.val s+rowUnitClip v*r.1.val s)| = _
  dsimp only
  rw [←abs_mul]
  congr 1
  ring

lemma rowProfileMix_parameter_tendsto {Q : ℝ} (q r : RowProfile Q) {t : ℝ} {ts : ℕ → ℝ}
    (ht : Tendsto ts atTop (𝓝 t)) :
    Tendsto (fun n => sphericalProfileDistance (rowProfileMix q r (ts n)).1.val (rowProfileMix q r t).1.val) atTop (𝓝 0) := by
  simp_rw [rowProfileMix_parameter_distance]
  simpa using (((rowUnitClip_continuous.tendsto t).comp ht).sub (tendsto_const_nhds (x := rowUnitClip t))).abs.mul_const
    (sphericalProfileDistance r.1.val q.1.val)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma rowFunctional_converges {u : ℝ → ℝ} {L H : ℝ} (hu : ContDiff ℝ 2 u)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    {Q : ℝ} (P : ℕ → RowFiniteProfile Q) (q : RowProfile Q)
    (hP : Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.1.val) atTop (𝓝 0)) :
    ∃ b : ℝ, Tendsto (fun n => (P n).functional u) atTop (𝓝 b) := by
  simpa only [rowFiniteFunctional u L H hu hL hH hb] using rowLog_converges hu hL hH hb P q.1 q.2 hP

lemma rowFunctionalLimits_eq {u : ℝ → ℝ} {L H : ℝ} (hu : ContDiff ℝ 2 u)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    {Q : ℝ} (P R : ℕ → RowFiniteProfile Q) (q : RowProfile Q) {a b : ℝ}
    (hP : Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.1.val) atTop (𝓝 0))
    (hR : Tendsto (fun n => sphericalProfileDistance (R n).profile.val q.1.val) atTop (𝓝 0))
    (hPa : Tendsto (fun n => (P n).functional u) atTop (𝓝 a))
    (hRb : Tendsto (fun n => (R n).functional u) atTop (𝓝 b)) : a=b := by
  let Z : ℕ → RowFiniteProfile Q := fun n => if n%2=0 then P n else R n
  have hZ : Tendsto (fun n => sphericalProfileDistance (Z n).profile.val q.1.val) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sphericalProfileDistance_nonneg _ _) (fun n => ?_)
      (show Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.1.val +
        sphericalProfileDistance (R n).profile.val q.1.val) atTop (𝓝 0) by simpa using hP.add hR)
    dsimp [Z]
    split_ifs
    · exact le_add_of_nonneg_right (sphericalProfileDistance_nonneg _ _)
    · exact le_add_of_nonneg_left (sphericalProfileDistance_nonneg _ _)
  obtain ⟨c,hc⟩ := rowFunctional_converges hu hL hH hb Z q hZ
  have hte : Tendsto (fun n : ℕ => 2*n) atTop atTop := tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hto : Tendsto (fun n : ℕ => 2*n+1) atTop atTop := tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have he : ∀ n, Z (2*n) = P (2*n) := by intro n; simp [Z]
  have ho : ∀ n, Z (2*n+1) = R (2*n+1) := by intro n; simp [Z,Nat.add_mod]
  have ha : a=c := tendsto_nhds_unique (hPa.comp hte) (by simpa only [Function.comp_def,he] using hc.comp hte)
  have hb' : b=c := tendsto_nhds_unique (hRb.comp hto) (by simpa only [Function.comp_def,ho] using hc.comp hto)
  exact ha.trans hb'.symm

lemma rowGeneralFunctional {u : ℝ → ℝ} {L H : ℝ} (hu : ContDiff ℝ 2 u)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    (Q : ℝ) : ∃ Phi : RowProfile Q → ℝ,
    (∀ (q : RowProfile Q) (P : ℕ → RowFiniteProfile Q),
      Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.1.val) atTop (𝓝 0) →
      Tendsto (fun n => (P n).functional u) atTop (𝓝 (Phi q))) ∧
    (∀ (q : RowProfile Q) (qn : ℕ → RowProfile Q),
      Tendsto (fun n => sphericalProfileDistance (qn n).1.val q.1.val) atTop (𝓝 0) →
      Tendsto (fun n => Phi (qn n)) atTop (𝓝 (Phi q))) := by
  have hex (q : RowProfile Q) := rowFunctional_converges hu hL hH hb (q.1.rowGrid q.2) q (rowGrid_distance_tendsto q.1 q.2)
  choose Phi hPhi using hex
  have hall (q : RowProfile Q) (P : ℕ → RowFiniteProfile Q)
      (hP : Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.1.val) atTop (𝓝 0)) :
      Tendsto (fun n => (P n).functional u) atTop (𝓝 (Phi q)) := by
    obtain ⟨a,ha⟩ := rowFunctional_converges hu hL hH hb P q hP
    have he := rowFunctionalLimits_eq hu hL hH hb P (q.1.rowGrid q.2) q hP (rowGrid_distance_tendsto q.1 q.2) ha (hPhi q)
    rwa [he] at ha
  refine ⟨Phi,hall,?_⟩
  intro q qn hqn
  have hchoose (n : ℕ) : ∃ k : ℕ,
      sphericalProfileDistance ((qn n).1.rowGrid (qn n).2 k).profile.val (qn n).1.val < 1/((n:ℝ)+1) ∧
      |((qn n).1.rowGrid (qn n).2 k).functional u-Phi (qn n)| < 1/((n:ℝ)+1) := by
    have he : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
    have hlim : Tendsto (fun k => |((qn n).1.rowGrid (qn n).2 k).functional u-Phi (qn n)|) atTop (𝓝 0) := by
      simpa using ((hPhi (qn n)).sub (tendsto_const_nhds (x := Phi (qn n)))).abs
    exact (((tendsto_order.mp (rowGrid_distance_tendsto (qn n).1 (qn n).2)).2 _ he).and
      ((tendsto_order.mp hlim).2 _ he)).exists
  choose k hk1 hk2 using hchoose
  let P : ℕ → RowFiniteProfile Q := fun n => (qn n).1.rowGrid (qn n).2 (k n)
  have hP : Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.1.val) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sphericalProfileDistance_nonneg _ _) (fun n => ?_)
      (show Tendsto (fun n : ℕ => 1/((n:ℝ)+1)+sphericalProfileDistance (qn n).1.val q.1.val) atTop (𝓝 0)
        by simpa using rowPrecision_tendsto.add hqn)
    exact (sphericalProfileDistance_triangle (P n).profile (qn n).1 q.1).trans (add_le_add (hk1 n).le le_rfl)
  have hlim : Tendsto (fun n => Phi (qn n)-(P n).functional u) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) rowPrecision_tendsto
    simpa only [Real.norm_eq_abs,abs_sub_comm] using (hk2 n).le
  have hh := hlim.add (hall q P hP)
  simpa only [sub_add_cancel,zero_add] using hh
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma rowProfile_mul_integrable (p q : SphericalProfile) :
    IntervalIntegrable (fun s => p.val s*q.val s) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)]
  have hi := q.integrable.1
  apply p.integrable.1.mul_bdd hi.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs,abs_of_nonneg (q.nonneg s ⟨hs.1.le,hs.2⟩)]
  exact q.mono ⟨hs.1.le,hs.2⟩ (by norm_num) hs.2

lemma rowDirection_integrable (q r D : SphericalProfile) :
    IntervalIntegrable (fun s => (r.val s-q.val s)*D.val s) volume 0 1 := by
  simpa only [sub_mul] using (rowProfile_mul_integrable r D).sub (rowProfile_mul_integrable q D)

def rowDirectionPairing (q r D : SphericalProfile) : ℝ :=
  ∫ s in (0:ℝ)..1, (r.val s-q.val s)*D.val s

lemma rowDirectionPairing_bound (q r D : SphericalProfile) {B : ℝ}
    (hD : ∀ s ∈ Set.Icc (0:ℝ) 1, D.val s ≤ B) :
    |rowDirectionPairing q r D| ≤ B*sphericalProfileDistance r.val q.val := by
  unfold rowDirectionPairing sphericalProfileDistance
  rw [←intervalIntegral.integral_const_mul]
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans ?_
  apply intervalIntegral.integral_mono_on (by norm_num) (rowDirection_integrable q r D).abs
    ((r.integrable.sub q.integrable).abs.const_mul B)
  intro s hs
  try dsimp only
  rw [abs_mul,abs_of_nonneg (D.nonneg s hs)]
  nlinarith [abs_nonneg (r.val s-q.val s),hD s hs]

lemma rowDirectionPairing_difference_bound (q r p v D E : SphericalProfile) {B C : ℝ}
    (hD : ∀ s ∈ Set.Icc (0:ℝ) 1, D.val s ≤ B)
    (hpv : ∀ s ∈ Set.Icc (0:ℝ) 1, |v.val s-p.val s| ≤ C) :
    |rowDirectionPairing q r D-rowDirectionPairing p v E| ≤
      B*(sphericalProfileDistance r.val v.val+sphericalProfileDistance q.val p.val)+
        C*sphericalProfileDistance D.val E.val := by
  unfold rowDirectionPairing sphericalProfileDistance
  rw [←intervalIntegral.integral_sub (rowDirection_integrable q r D) (rowDirection_integrable p v E)]
  rw [mul_add,←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul,
    ←intervalIntegral.integral_const_mul]
  rw [←intervalIntegral.integral_add ((r.integrable.sub v.integrable).abs.const_mul B)
    ((q.integrable.sub p.integrable).abs.const_mul B)]
  rw [←intervalIntegral.integral_add
    (((r.integrable.sub v.integrable).abs.const_mul B).add ((q.integrable.sub p.integrable).abs.const_mul B))
    ((D.integrable.sub E.integrable).abs.const_mul C)]
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans ?_
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((rowDirection_integrable q r D).sub (rowDirection_integrable p v E)).abs
    ((((r.integrable.sub v.integrable).abs.const_mul B).add ((q.integrable.sub p.integrable).abs.const_mul B)).add ((D.integrable.sub E.integrable).abs.const_mul C))
  intro s hs
  try dsimp only
  have hd := D.nonneg s hs
  calc
    _ = |((r.val s-v.val s)-(q.val s-p.val s))*D.val s+(v.val s-p.val s)*(D.val s-E.val s)| := by congr 1; ring
    _ ≤ |((r.val s-v.val s)-(q.val s-p.val s))*D.val s|+|(v.val s-p.val s)*(D.val s-E.val s)| := abs_add_le _ _
    _ = |(r.val s-v.val s)-(q.val s-p.val s)| *D.val s+|v.val s-p.val s| *|D.val s-E.val s| := by rw [abs_mul,abs_mul,abs_of_nonneg hd]
    _ ≤ (|r.val s-v.val s|+|q.val s-p.val s|)*D.val s+C*|D.val s-E.val s| :=
      add_le_add (mul_le_mul_of_nonneg_right (abs_sub _ _) hd)
        (mul_le_mul_of_nonneg_right (hpv s hs) (abs_nonneg _))
    _ ≤ (|r.val s-v.val s|+|q.val s-p.val s|)*B+C*|D.val s-E.val s| :=
      add_le_add (mul_le_mul_of_nonneg_left (hD s hs) (add_nonneg (abs_nonneg _) (abs_nonneg _))) le_rfl
    _ = _ := by ring

lemma rowProfile_difference_bound {Q : ℝ} (q r : RowProfile Q) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    |r.1.val s-q.1.val s| ≤ Q := by
  have hq := (q.1.mono hs (by norm_num) hs.2).trans q.2
  have hr := (r.1.mono hs (by norm_num) hs.2).trans r.2
  exact abs_le.mpr ⟨by linarith [r.1.nonneg s hs],by linarith [q.1.nonneg s hs]⟩

lemma rowDirectionPairing_tendsto {Q B : ℝ} (q r : RowProfile Q) (D : SphericalProfile)
    (qn rn : ℕ → RowProfile Q) (Dn : ℕ → SphericalProfile)
    (hD : ∀ n s, s ∈ Set.Icc (0:ℝ) 1 → (Dn n).val s ≤ B)
    (hq : Tendsto (fun n => sphericalProfileDistance (qn n).1.val q.1.val) atTop (𝓝 0))
    (hr : Tendsto (fun n => sphericalProfileDistance (rn n).1.val r.1.val) atTop (𝓝 0))
    (hd : Tendsto (fun n => sphericalProfileDistance (Dn n).val D.val) atTop (𝓝 0)) :
    Tendsto (fun n => rowDirectionPairing (qn n).1 (rn n).1 (Dn n)) atTop (𝓝 (rowDirectionPairing q.1 r.1 D)) := by
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (show Tendsto (fun n => B*(sphericalProfileDistance (rn n).1.val r.1.val+sphericalProfileDistance (qn n).1.val q.1.val)+Q*sphericalProfileDistance (Dn n).val D.val) atTop (𝓝 0) by
      simpa using ((hr.add hq).const_mul B).add (hd.const_mul Q))
  rw [Real.norm_eq_abs]
  exact rowDirectionPairing_difference_bound _ _ _ _ _ _ (hD n) (fun s hs => rowProfile_difference_bound q r hs)
end MicroscopicJamming

end

end OAI
