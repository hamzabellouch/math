import OAI.Probability.GaussianReplacement.Refinement

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def criticalSignal {d : ℕ} {W : Type*} [MeasurableSpace W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ) : Measure (Sphere d×(W×(ℕ×ℤ))) :=
  refineSignal P (criticalRefinement P ℓ)

instance criticalSignal_probability {d : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (ℓ : ℕ) :
    IsProbabilityMeasure (criticalSignal P ℓ) :=
  refineSignal_probability P _ (measurable_criticalRefinement P ℓ)

def criticalB {d : ℕ} {W : Type*} [MeasurableSpace W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ) (v : W×(ℕ×ℤ)) : ℝ :=
  Real.exp ((v.2.2:ℝ)+(ℓ:ℝ)*Real.log 4+refinementLoss P (criticalRefinement P ℓ) v)

def criticalD {d : ℕ} {W : Type*} [MeasurableSpace W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ) (v : W×(ℕ×ℤ)) : ℝ :=
  Real.exp (-Real.log ((criticalSignal P ℓ).snd {v}).toReal)*(3*4^d)

lemma criticalSignal_fst {d : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (ℓ : ℕ) :
    (criticalSignal P ℓ).fst = P.fst :=
  refineSignal_fst P _ (measurable_criticalRefinement P ℓ)

lemma criticalSignal_posterior {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0) :
    messagePosterior (criticalSignal P ℓ) v = criticalPosterior (messagePosterior P v.1) ℓ v.2.1 v.2.2 ∧
    0 < messagePosterior P v.1 (criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2) ∧
    P.snd {v.1} ≠ 0 := by
  have he := measurable_criticalRefinement P ℓ
  have hw := refineSignal_positive_original P _ he hv
  have hc : {s : Sphere d | criticalRefinement P ℓ (s,v.1) = v.2} =
      criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2 := by
    ext s
    simp only [criticalRefinement,criticalClass,mem_ofPred_eq,Prod.ext_iff]
  have hmass := refineSignal_mass P _ he hw v.2
  rw [hc] at hmass
  change (criticalSignal P ℓ).snd {v} = _ at hmass
  have hη : messagePosterior P v.1 (criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2) ≠ 0 := by
    intro hz
    rw [hmass,hz,mul_zero] at hv
    exact hv rfl
  refine ⟨?_,hη.bot_lt,hw⟩
  have hp := messagePosterior_refinement P _ he hv
  rw [hc] at hp
  exact hp

lemma criticalB_eq {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0) :
    criticalB P ℓ v = (4:ℝ)^ℓ * Real.exp (v.2.2:ℝ) /
      (messagePosterior P v.1 (criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2)).toReal := by
  have he := measurable_criticalRefinement P ℓ
  have hc : {s : Sphere d | criticalRefinement P ℓ (s,v.1) = v.2} =
      criticalClass (messagePosterior P v.1) ℓ v.2.1 v.2.2 := by
    ext s
    simp only [criticalRefinement,criticalClass,mem_ofPred_eq,Prod.ext_iff]
  have hδ := refinementLoss_eq P _ he hv
  rw [hc] at hδ
  have hη := (criticalSignal_posterior P hv).2.1
  have hηr := ENNReal.toReal_pos hη.ne' (measure_ne_top _ _)
  unfold criticalB
  rw [hδ,Real.exp_add,Real.exp_add,Real.exp_neg,Real.exp_log hηr,
    ←Real.log_pow,Real.exp_log (by positivity : (0:ℝ)<4^ℓ)]
  ring

lemma criticalD_eq {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0) :
    criticalD P ℓ v = ((criticalSignal P ℓ).snd {v}).toReal⁻¹*(3*4^d) := by
  rw [criticalD,Real.exp_neg,Real.exp_log (ENNReal.toReal_pos hv (measure_ne_top _ _))]

lemma criticalFamily_growth {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0) :
    LocalGrowth (messagePosterior (criticalSignal P ℓ) v) ℓ (criticalB P ℓ v) ∧
    LocalGrowth (messagePosterior (criticalSignal P ℓ) v) (d-1) (criticalD P ℓ v) ∧
    0 ≤ (v.2.2:ℝ)+(ℓ:ℝ)*Real.log 4+refinementLoss P (criticalRefinement P ℓ) v ∧
    messagePosterior (criticalSignal P ℓ) v ≪ uniformSphere d := by
  obtain ⟨hpost,hη,hw⟩ := criticalSignal_posterior P hv
  have hd : 1 ≤ d := by omega
  have hg := posterior_sphere_growth P hσ hd hw
  let D := (P.snd {v.1}).toReal⁻¹*(3*4^d)
  have hD : 1 ≤ D := by
    have ha := ENNReal.toReal_pos hw (measure_ne_top _ _)
    have ha1 : (P.snd {v.1}).toReal ≤ 1 := by
      exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using (prob_le_one : P.snd {v.1} ≤ 1))
    have hinv : 1 ≤ (P.snd {v.1}).toReal⁻¹ := (one_le_inv₀ ha).mpr ha1
    have hp : (1:ℝ) ≤ 4^d := one_le_pow₀ (by norm_num)
    dsimp only [D]
    nlinarith
  have hsigma : (criticalSignal P ℓ).fst = uniformSphere d := (criticalSignal_fst P ℓ).trans hσ
  refine ⟨?_,?_,?_,?_⟩
  · rw [hpost,criticalB_eq P hv]
    exact criticalPosterior_growth (messagePosterior P v.1) D (by linarith) hg hℓ v.2.2 hη
  · rw [criticalD_eq P hv]
    exact posterior_sphere_growth (criticalSignal P ℓ) hsigma hd hv
  · obtain ⟨s,hs⟩ := nonempty_of_measure_ne_zero hη.ne'
    have hq := (criticalLevel_bounds (messagePosterior P v.1) D hD hg hℓ s).1
    rw [hs.2] at hq
    have hl4 : 1 ≤ Real.log 4 := by
      have hh : Real.log 4 = 2*Real.log 2 := by
        have hh := (Real.log_pow (2:ℝ) 2)
        norm_num at hh ⊢
        exact hh
      linarith [Real.log_two_gt_d9]
    have ht := refinementLoss_nonneg P _ (measurable_criticalRefinement P ℓ) hv
    nlinarith [Nat.cast_nonneg (α:=ℝ) ℓ]
  · have hh := messagePosterior_le (criticalSignal P ℓ) hv
    rw [hsigma] at hh
    exact hh.absolutelyContinuous.trans Measure.smul_absolutelyContinuous

lemma criticalSignal_entropy {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) (hH : shannonEntropy P.snd ≠ ∞) :
    shannonEntropy (P.map (criticalRefinement P ℓ)) ≠ ∞ ∧
    (shannonEntropy (P.map (criticalRefinement P ℓ))).toReal ≤
      1+2*Real.log (20*((d:ℝ)+1+(shannonEntropy P.snd).toReal)+1) ∧
    shannonEntropy (criticalSignal P ℓ).snd ≠ ∞ ∧
    (shannonEntropy (criticalSignal P ℓ).snd).toReal ≤ (shannonEntropy P.snd).toReal+
      (shannonEntropy (P.map (criticalRefinement P ℓ))).toReal := by
  obtain ⟨he,hb⟩ := criticalRefinement_entropy P hσ hℓ hH
  obtain ⟨hp,hpb,_,_⟩ := refinement_entropy_and_loss P _ (measurable_criticalRefinement P ℓ) hH he
  exact ⟨he,hb,hp,hpb⟩

lemma criticalLevel_integrable {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) (hH : shannonEntropy P.snd ≠ ∞) :
    Integrable (fun v : W×(ℕ×ℤ) => (v.2.2:ℝ)) (criticalSignal P ℓ).snd := by
  let e := criticalRefinement P ℓ
  have he := measurable_criticalRefinement P ℓ
  have hw : Integrable (fun p : Sphere d×W => -Real.log (P.snd {p.2}).toReal) P :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable measurable_snd.aemeasurable).mp
      (entropy_finite_integrable P.snd hH)
  have hbi : Integrable (fun p : Sphere d×W => 20*((d:ℝ)+1-Real.log (P.snd {p.2}).toReal)) P := by
    convert ((integrable_const ((d:ℝ)+1)).add hw).const_mul 20 using 1
  have hqi : Integrable (fun p => ((e p).2:ℝ)) P := by
    apply hbi.mono' ((measurable_of_countable (fun x : ℕ×ℤ => (x.2:ℝ))).comp he).aestronglyMeasurable
    have hp := (ae_map_iff measurable_snd.aemeasurable ((Set.to_countable _).measurableSet)).mp
      (ae_positive_atom P.snd)
    filter_upwards [hp] with p hp
    have hb := criticalRefinement_size P hσ hℓ hp
    change ‖((e p).2:ℝ)‖ ≤ _
    rw [Real.norm_eq_abs]
    have habs : |((e p).2:ℝ)| = ((e p).2.natAbs:ℝ) := by simp
    rw [habs]
    change ((e p).1:ℝ)+2*((e p).2.natAbs:ℝ) ≤ _ at hb
    nlinarith [Nat.cast_nonneg (α:=ℝ) (e p).1,Nat.cast_nonneg (α:=ℝ) (e p).2.natAbs]
  change Integrable _ (refineSignal P e).snd
  rw [refineSignal_snd P e he]
  exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_snd.prodMk he).aemeasurable).mpr hqi

lemma criticalFamily_moment_mean {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) (hH : shannonEntropy P.snd ≠ ∞) :
    Integrable (fun v => Real.log (1+momentBound 9 d (criticalB P ℓ v) (criticalD P ℓ v)))
      (criticalSignal P ℓ).snd ∧
    (∫ v, Real.log (1+momentBound 9 d (criticalB P ℓ v) (criticalD P ℓ v)) ∂(criticalSignal P ℓ).snd) ≤
      (∫ v : W×(ℕ×ℤ), (v.2.2:ℝ) ∂(criticalSignal P ℓ).snd) +
      (shannonEntropy (P.map (criticalRefinement P ℓ))).toReal + 18*d +
      Real.log (1+(shannonEntropy (criticalSignal P ℓ).snd).toReal) := by
  let π := (criticalSignal P ℓ).snd
  let e := criticalRefinement P ℓ
  let s : W×(ℕ×ℤ) → ℝ := fun v => -Real.log (π {v}).toReal
  have hs : Integrable s π := entropy_finite_integrable π (criticalSignal_entropy P hσ hℓ hH).2.2.1
  have hsm : Measurable s := measurable_of_countable _
  have hs0 : ∀ v, 0 ≤ s v := atom_surprisal_nonneg π
  have hlog := integrable_log_one_add_real π hs hsm (Eventually.of_forall hs0)
  have hlogmean := integral_log_one_add_real_le π hs hsm (Eventually.of_forall hs0)
  have hsmean : (∫ v, s v ∂π) = (shannonEntropy π).toReal := integral_surprisal π
  rw [hsmean] at hlogmean
  obtain ⟨_,_,hδ,hδmean⟩ := refinement_entropy_and_loss P e (measurable_criticalRefinement P ℓ) hH
    (criticalSignal_entropy P hσ hℓ hH).1
  have hqi := criticalLevel_integrable P hσ hℓ hH
  have hupper : Integrable (fun v : W×(ℕ×ℤ) => ((v.2.2:ℝ)+refinementLoss P e v)+18*d+Real.log (1+s v)) π :=
    ((hqi.add hδ).add (integrable_const _)).add hlog
  have hle : ∀ᵐ v ∂π,
      Real.log (1+momentBound 9 d (criticalB P ℓ v) (criticalD P ℓ v)) ≤
        ((v.2.2:ℝ)+refinementLoss P e v)+18*d+Real.log (1+s v) := by
    filter_upwards [ae_positive_atom π] with v hv
    have hb := (criticalFamily_growth P hσ hℓ hv).2.2.1
    exact critical_moment_log_bound (by omega) (by omega) _ _ _
      (hs0 v) hb
  have hL : Integrable (fun v => Real.log (1+momentBound 9 d (criticalB P ℓ v) (criticalD P ℓ v))) π := by
    apply hupper.mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [hle] with v hv
    have hB : 0 ≤ criticalB P ℓ v := (Real.exp_pos _).le
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg
      (le_add_of_nonneg_right (momentBound_nonneg 9 d hB)))]
    exact hv
  refine ⟨hL,?_⟩
  have hh := integral_mono_ae hL hupper hle
  have hqδ : Integrable (fun v : W×(ℕ×ℤ) => (v.2.2:ℝ)+refinementLoss P e v) π := hqi.add hδ
  have hu : Integrable (fun v : W×(ℕ×ℤ) => (v.2.2:ℝ)+refinementLoss P e v+18*(d:ℝ)) π :=
    hqδ.add (integrable_const _)
  rw [integral_add hu hlog,integral_add hqδ (integrable_const (18*(d:ℝ))),integral_add hqi hδ,
    integral_const,probReal_univ,one_smul] at hh
  exact hh.trans (add_le_add (add_le_add (add_le_add le_rfl hδmean) le_rfl) hlogmean)


lemma completeFamily_restrict_apply {W T : Type*} [MeasurableSpace W]
    (π : Measure W) (f : W → T) (t₀ : T) {w : W} (hw : π {w} ≠ 0) :
    completeFamily π (fun v => f v.1) t₀ w = f w := by
  have hp : 0 < π {w} := pos_iff_ne_zero.mpr hw
  rw [completeFamily, dite_eq_left hp]

lemma completeFamily_restrict_ae {W T : Type*} [MeasurableSpace W] [Countable W]
    [MeasurableSingletonClass W] (π : Measure W) (f : W → T) (t₀ : T) :
    completeFamily π (fun v => f v.1) t₀ =ᵐ[π] f := by
  filter_upwards [ae_positive_atom π] with w hw
  exact completeFamily_restrict_apply π f t₀ hw

lemma actual_posterior_completed {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d)
    (hH : shannonEntropy P.fst.snd ≠ ∞)
    (B D : W → ℝ)
    (hB : ∀ w, P.fst.snd {w} ≠ 0 → 0 < B w)
    (hD : ∀ w, P.fst.snd {w} ≠ 0 → 0 < D w)
    (hAC : ∀ w, P.fst.snd {w} ≠ 0 → messagePosterior P.fst w ≪ uniformSphere d)
    (hgB : ∀ w, P.fst.snd {w} ≠ 0 → LocalGrowth (messagePosterior P.fst w) (m+r) (B w))
    (hgD : ∀ w, P.fst.snd {w} ≠ 0 → LocalGrowth (messagePosterior P.fst w) (d-1) (D w))
    (hCI : Integrable (fun w => Real.log (1+momentBound 9 d (B w) (D w))) P.fst.snd) :
    ActualRowConclusion (r:=r) (q:=q) P
      (completeFamily (P.map swapLast).snd (fun w => messagePosterior P.fst w.1) 0)
      (completeFamily (P.map swapLast).snd (fun w => B w.1) 1)
      (completeFamily (P.map swapLast).snd (fun w => D w.1) 1) := by
  let π := (P.map swapLast).snd
  have hπ : π = P.fst.snd := swapLast_snd P
  let ρ : PositiveMessage π → Measure (Sphere d) := fun w => messagePosterior P.fst w.1
  let b : PositiveMessage π → ℝ := fun w => B w.1
  let c : PositiveMessage π → ℝ := fun w => D w.1
  have hw (w : PositiveMessage π) : P.fst.snd {w.1} ≠ 0 := by rw [←hπ]; exact w.2.ne'
  let f : W → ℝ := fun w => Real.log (1+momentBound 9 d (B w) (D w))
  let f' : W → ℝ := fun w => Real.log (1+momentBound 9 d
    (completeFamily π b 1 w) (completeFamily π c 1 w))
  have hf : f' =ᵐ[π] f := by
    filter_upwards [ae_positive_atom π] with w hw
    dsimp only [f',f,b,c]
    rw [completeFamily_restrict_apply π B 1 hw,completeFamily_restrict_apply π D 1 hw]
  have hfbase : (fun sw : Sphere d×W => f' sw.2) =ᵐ[P.fst] (fun sw => f sw.2) := by
    apply (ae_map_iff measurable_snd.aemeasurable (measurableSet_eq_fun
      (measurable_of_countable f') (measurable_of_countable f))).mp
    change f' =ᵐ[P.fst.snd] f
    rw [←hπ]
    exact hf
  have hCI' : Integrable (fun sw : Sphere d×W => f' sw.2) P.fst := by
    apply Integrable.congr _ hfbase.symm
    exact (integrable_map_measure (measurable_of_countable f).aestronglyMeasurable
      measurable_snd.aemeasurable).mp hCI
  exact actualRowMain hdim P ν hInd H hν (by rwa [swapLast_snd]) ρ
    (fun w => hAC w.1 (hw w)) b c (fun w => hB w.1 (hw w)) (fun w => hD w.1 (hw w))
    (fun w => hgB w.1 (hw w)) (fun w => hgD w.1 (hw w)) hCI'

lemma actualRowConclusion_observed {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ρ : W → Measure (Sphere d)) [∀ w, IsFiniteMeasure (ρ w)] (B D : W → ℝ)
    (hmain : ActualRowConclusion (r:=r) (q:=q) P ρ B D) :
    Integrable (fun z => Real.log (1+(exactDensity (ρ z.2) z.1.1 z.1.2).toReal))
      (observedMessage (alignedExperiment (r:=r) P)) ∧
    Integrable (fun z => logPositive (exactDensity (ρ z.2) z.1.1 z.1.2))
      (observedMessage (alignedExperiment (r:=r) P)) ∧
    (∫ z, Real.log (1+(exactDensity (ρ z.2) z.1.1 z.1.2).toReal)
      ∂observedMessage (alignedExperiment (r:=r) P)) ≤
        (rowInformation P (gaussianRows m d)).toReal/q +
          ∫ w, Real.log (1+momentBound 9 d (B w) (D w)) ∂P.fst.snd := by
  let O := observedMessage (alignedExperiment (r:=r) P)
  let p : (Rows (m+r) d×(Fin (m+r)→ℝ))×W → ℝ≥0∞ :=
    fun z => exactDensity (ρ z.2) z.1.1 z.1.2
  have hp : Measurable p := measurable_from_prod_countable_left fun w => measurable_exactDensity (k:=m+r) (ρ w)
  let T : ((Sphere d×W)×Rows m d)×Rows r d → (Rows (m+r) d×(Fin (m+r)→ℝ))×W :=
    observedMessageMap ∘ (fun p => (p.1.1,Fin.append p.1.2 p.2))
  have hT : Measurable T := measurable_observedMessageMap.comp measurable_alignedMap
  have hO : O = (actualExperiment (r:=r) P).map T := by
    dsimp only [O]
    rw [observedMessage,alignedExperiment,Measure.map_map measurable_observedMessageMap measurable_alignedMap]
  have hLi : Integrable (fun z => Real.log (1+(p z).toReal)) O := by
    rw [hO]
    apply (integrable_map_measure (measurable_log_one_add hp).aestronglyMeasurable
      hT.aemeasurable).mpr
    exact hmain.exact_integrable
  have hPi : Integrable (fun z => logPositive (p z)) O := by
    rw [hO]
    apply (integrable_map_measure ((hp.ennreal_toReal.log.max measurable_const).aestronglyMeasurable) hT.aemeasurable).mpr
    exact hmain.positive_log_integrable
  refine ⟨hLi,hPi,?_⟩
  change (∫ z, Real.log (1+(p z).toReal) ∂O) ≤ _
  rw [hO,integral_map hT.aemeasurable (measurable_log_one_add hp).aestronglyMeasurable]
  have hb := hmain.exact_bound
  rw [←integral_map measurable_snd.aemeasurable (measurable_of_countable
    (fun w => Real.log (1+momentBound 9 d (B w) (D w)))).aestronglyMeasurable] at hb
  exact hb

lemma observedMessage_aligned_positive {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    ∀ᵐ z ∂observedMessage (alignedExperiment (r:=r) P), (P.map swapLast).snd {z.2} ≠ 0 := by
  have hpos : ∀ᵐ w ∂(observedMessage (alignedExperiment (r:=r) P)).snd, (P.map swapLast).snd {w} ≠ 0 := by
    rw [observedMessage_snd,alignedExperiment_fst,swapLast_snd]
    exact ae_positive_atom P.fst.snd
  exact (ae_map_iff measurable_snd.aemeasurable
    (Set.to_countable {w : W | (P.map swapLast).snd {w} ≠ 0}).measurableSet).mp hpos



lemma actual_posterior_log_bound {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d)
    (hH : shannonEntropy P.fst.snd ≠ ∞)
    (B D : W → ℝ)
    (hB : ∀ w, P.fst.snd {w} ≠ 0 → 0 < B w)
    (hD : ∀ w, P.fst.snd {w} ≠ 0 → 0 < D w)
    (hAC : ∀ w, P.fst.snd {w} ≠ 0 → messagePosterior P.fst w ≪ uniformSphere d)
    (hgB : ∀ w, P.fst.snd {w} ≠ 0 → LocalGrowth (messagePosterior P.fst w) (m+r) (B w))
    (hgD : ∀ w, P.fst.snd {w} ≠ 0 → LocalGrowth (messagePosterior P.fst w) (d-1) (D w))
    (hCI : Integrable (fun w => Real.log (1+momentBound 9 d (B w) (D w))) P.fst.snd) :
    Integrable (fun z => Real.log (1+(exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2).toReal))
      (observedMessage (alignedExperiment (r:=r) P)) ∧
    Integrable (fun z => logPositive (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2))
      (observedMessage (alignedExperiment (r:=r) P)) ∧
    (∫ z, Real.log (1+(exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2).toReal)
      ∂observedMessage (alignedExperiment (r:=r) P)) ≤
        (rowInformation P (gaussianRows m d)).toReal/q +
          ∫ w, Real.log (1+momentBound 9 d (B w) (D w)) ∂P.fst.snd := by
  let π := (P.map swapLast).snd
  let ρ' := completeFamily π (fun w => messagePosterior P.fst w.1) 0
  let B' := completeFamily π (fun w => B w.1) 1
  let D' := completeFamily π (fun w => D w.1) 1
  have hmain := actual_posterior_completed hdim P ν hInd H hν hH B D hB hD hAC hgB hgD hCI
  obtain ⟨hLi,hPi,hBound⟩ := actualRowConclusion_observed P ρ' B' D' hmain
  have heqp : (fun z => exactDensity (ρ' z.2) z.1.1 z.1.2) =ᵐ[observedMessage (alignedExperiment (r:=r) P)]
      (fun z => exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2) := by
    filter_upwards [observedMessage_aligned_positive (r:=r) P] with z hz
    dsimp only [ρ']
    rw [completeFamily_restrict_apply π (messagePosterior P.fst) 0 hz]
  have heqlog := heqp.mono (fun z hz => congrArg (fun t : ℝ≥0∞ => Real.log (1+t.toReal)) hz)
  have heqpos := heqp.mono (fun z hz => congrArg logPositive hz)
  refine ⟨hLi.congr heqlog,hPi.congr heqpos,?_⟩
  have hf : (fun w => Real.log (1+momentBound 9 d (B' w) (D' w))) =ᵐ[P.fst.snd]
      (fun w => Real.log (1+momentBound 9 d (B w) (D w))) := by
    rw [←swapLast_snd P]
    filter_upwards [ae_positive_atom π] with w hw
    dsimp only [B',D']
    rw [completeFamily_restrict_apply π B 1 hw,completeFamily_restrict_apply π D 1 hw]
  rw [integral_congr_ae heqlog,integral_congr_ae hf] at hBound
  exact hBound


lemma criticalFamily_cover_fibre {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) {v : W×(ℕ×ℤ)} (hv : (criticalSignal P ℓ).snd {v} ≠ 0)
    (hac : ∀ᵐ G ∂gaussianRows ℓ d, labelLaw (messagePosterior (criticalSignal P ℓ) v) G ≪ volume)
    (hpi : Integrable (fun z : Rows ℓ d×(Fin ℓ→ℝ) => logPositive
      (exactDensity (messagePosterior (criticalSignal P ℓ) v) z.1 z.2))
      (projectionJoint (messagePosterior (criticalSignal P ℓ) v) (gaussianRows ℓ d))) :
    -(∫ z, Real.log (exactDensity (messagePosterior (criticalSignal P ℓ) v) z.1 z.2).toReal
      ∂projectionJoint (messagePosterior (criticalSignal P ℓ) v) (gaussianRows ℓ d)) ≤
      1+5*(ℓ:ℝ)-(v.2.2:ℝ) := by
  let R := criticalSignal P ℓ
  obtain ⟨hpost,hη,hw⟩ := criticalSignal_posterior P hv
  have hpi' : Integrable (fun z : Rows ℓ d×Sphere d => logPositive
      (exactDensity (messagePosterior R v) z.1 (label z.1 (z.2:Vector d))))
      ((gaussianRows ℓ d).prod (messagePosterior R v)) := by
    rw [projectionJoint] at hpi
    exact (integrable_map_measure ((measurable_exactDensity _).ennreal_toReal.log.max
      measurable_const).aestronglyMeasurable (measurable_fst.prodMk measurable_own_label).aemeasurable).mp hpi
  change ∀ᵐ G ∂gaussianRows ℓ d, labelLaw (messagePosterior R v) G ≪ volume at hac
  rw [show messagePosterior R v = criticalPosterior (messagePosterior P v.1) ℓ v.2.1 v.2.2 from hpost] at hpi' hac
  have hbound := (criticalPosterior_cover_entropy (messagePosterior P v.1)
    ((P.snd {v.1}).toReal⁻¹*(3*4^d)) (by positivity)
    (posterior_sphere_growth P hσ (by omega) hw) hℓ v.2.2 hη hac hpi').2
  rw [projectionJoint,integral_map (measurable_fst.prodMk measurable_own_label).aemeasurable
    (measurable_exactDensity _).ennreal_toReal.log.aestronglyMeasurable]
  simpa only [hpost] using hbound


lemma criticalFamily_cover_mean {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) (hH : shannonEntropy P.snd ≠ ∞)
    (hAC : ∀ᵐ v ∂(criticalSignal P ℓ).snd, ∀ᵐ G ∂gaussianRows ℓ d,
      labelLaw (messagePosterior (criticalSignal P ℓ) v) G ≪ volume)
    (hpos : Integrable (fun z => logPositive (exactDensity
      (messagePosterior (criticalSignal P ℓ) z.2) z.1.1 z.1.2))
      (observedMessage ((criticalSignal P ℓ).prod (gaussianRows ℓ d))))
    (hlog : Integrable (fun z => Real.log (exactDensity
      (messagePosterior (criticalSignal P ℓ) z.2) z.1.1 z.1.2).toReal)
      (observedMessage ((criticalSignal P ℓ).prod (gaussianRows ℓ d)))) :
    -(∫ z, Real.log (exactDensity (messagePosterior (criticalSignal P ℓ) z.2) z.1.1 z.1.2).toReal
      ∂observedMessage ((criticalSignal P ℓ).prod (gaussianRows ℓ d))) ≤
      1+5*(ℓ:ℝ)-(∫ v : W×(ℕ×ℤ), (v.2.2:ℝ) ∂(criticalSignal P ℓ).snd) := by
  let R := criticalSignal P ℓ
  let π := R.snd
  let κ := posteriorProjectionKernel R (gaussianRows ℓ d)
  let f : (W×(ℕ×ℤ))×(Rows ℓ d×(Fin ℓ→ℝ)) → ℝ :=
    fun z => Real.log (exactDensity (messagePosterior R z.1) z.2.1 z.2.2).toReal
  let fp : (W×(ℕ×ℤ))×(Rows ℓ d×(Fin ℓ→ℝ)) → ℝ :=
    fun z => logPositive (exactDensity (messagePosterior R z.1) z.2.1 z.2.2)
  have hm : Measurable (fun z : (Rows ℓ d×(Fin ℓ→ℝ))×(W×(ℕ×ℤ)) =>
      exactDensity (messagePosterior R z.2) z.1.1 z.1.2) :=
    measurable_from_prod_countable_left fun v => measurable_exactDensity (k:=ℓ) (messagePosterior R v)
  have hfi : Integrable f (π ⊗ₘ κ) := by
    rw [observedMessage_independent_disintegrate] at hlog
    exact (integrable_map_measure hm.ennreal_toReal.log.aestronglyMeasurable
      measurable_swap.aemeasurable).mp hlog
  have hfpi : Integrable fp (π ⊗ₘ κ) := by
    rw [observedMessage_independent_disintegrate] at hpos
    exact (integrable_map_measure (hm.ennreal_toReal.log.max measurable_const).aestronglyMeasurable
      measurable_swap.aemeasurable).mp hpos
  have hji : Integrable (fun v => ∫ z, f (v,z) ∂κ v) π := by
    simpa only [Kernel.prodMkLeft_apply,Kernel.const_apply] using hfi.integral_compProd
  have hposae : ∀ᵐ v ∂π, Integrable (fun z => fp (v,z)) (κ v) :=
    (Measure.integrable_compProd_iff hfpi.aestronglyMeasurable).mp hfpi |>.1
  have hb : ∀ᵐ v ∂π, -(∫ z, f (v,z) ∂κ v) ≤ 1+5*(ℓ:ℝ)-(v.2.2:ℝ) := by
    filter_upwards [ae_positive_atom π,hposae,hAC] with v hv hpi hac
    have hk : κ v = projectionJoint (messagePosterior R v) (gaussianRows ℓ d) :=
      posteriorProjectionKernel_apply R _ _
    dsimp only [fp] at hpi
    rw [hk] at hpi
    dsimp only [f]
    rw [hk]
    exact criticalFamily_cover_fibre P hσ hℓ hv hac hpi
  have hqi := criticalLevel_integrable P hσ hℓ hH
  have hupper : Integrable (fun v : W×(ℕ×ℤ) => 1+5*(ℓ:ℝ)-(v.2.2:ℝ)) π :=
    (integrable_const _).sub hqi
  have he := integral_mono_ae hji.neg hupper hb
  simp only [Pi.neg_apply] at he
  rw [integral_neg,integral_sub (integrable_const (1+5*(ℓ:ℝ))) hqi,
    integral_const,probReal_univ,one_smul] at he
  rw [observedMessage_independent_disintegrate,
    integral_map measurable_swap.aemeasurable hm.ennreal_toReal.log.aestronglyMeasurable]
  change -(∫ z, f z ∂π ⊗ₘ κ) ≤ _
  rw [Measure.integral_compProd hfi]
  exact he



def refineRows {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) (e : Sphere d×W → E) :
    Measure ((Sphere d×(W×E))×Rows m d) :=
  P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))

lemma measurable_refineRowsMap {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (e : Sphere d×W → E) (he : Measurable e) :
    Measurable (fun p : (Sphere d×W)×Rows m d => ((p.1.1,(p.1.2,e p.1)),p.2)) :=
  (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk (he.comp measurable_fst))).prodMk measurable_snd

lemma refineRows_probability {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (e : Sphere d×W → E) (he : Measurable e) : IsProbabilityMeasure (refineRows P e) := by
  unfold refineRows
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_refineRowsMap e he).aemeasurable).mpr inferInstance

lemma refineRows_fst {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) (e : Sphere d×W → E) (he : Measurable e) :
    (refineRows P e).fst = refineSignal P.fst e := by
  rw [refineRows,Measure.fst,refineSignal,Measure.fst,
    Measure.map_map measurable_fst (measurable_refineRowsMap e he),
    Measure.map_map (measurable_fst.prodMk (measurable_snd.prodMk he)) measurable_fst]
  rfl

lemma refineRows_signal_rows {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) (e : Sphere d×W → E) (he : Measurable e) :
    ((refineRows P e).map swapLast).fst = (P.map swapLast).fst := by
  rw [Measure.fst,Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map measurable_fst swapLast.measurable,refineRows,
    Measure.map_map (measurable_fst.comp swapLast.measurable) (measurable_refineRowsMap e he)]
  rfl

lemma refineRows_drop {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) (e : Sphere d×W → E) (he : Measurable e) :
    (refineRows P e).map (fun p => ((p.1.1,p.1.2.1),p.2)) = P := by
  rw [refineRows,Measure.map_map
    ((measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd)
    (measurable_refineRowsMap e he)]
  exact Measure.map_id

lemma alignedExperiment_drop {d m r : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×(W×E))×Rows m d)) [IsProbabilityMeasure P] :
    (alignedExperiment (r:=r) P).map (fun p => ((p.1.1,p.1.2.1),p.2)) =
      alignedExperiment (r:=r) (P.map (fun p => ((p.1.1,p.1.2.1),p.2))) := by
  let T : (Sphere d×(W×E))×Rows m d → (Sphere d×W)×Rows m d :=
    fun p => ((p.1.1,p.1.2.1),p.2)
  have hT : Measurable T := (measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd
  have hprod : (P.map T).prod (gaussianRows r d) =
      (P.prod (gaussianRows r d)).map (Prod.map T id) := by
    simpa only [Measure.map_id] using (Measure.map_prod_map P (gaussianRows r d) hT measurable_id)
  rw [alignedExperiment,Measure.map_map
    ((measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd) measurable_alignedMap]
  change _ = ((P.map T).prod (gaussianRows r d)).map _
  rw [hprod,Measure.map_map measurable_alignedMap (hT.prodMap measurable_id)]
  rfl

lemma independent_refineSignal_drop {d k : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (e : Sphere d×W → E) (he : Measurable e) :
    ((refineSignal P e).prod (gaussianRows k d)).map (fun p => ((p.1.1,p.1.2.1),p.2)) =
      P.prod (gaussianRows k d) := by
  let : IsFiniteMeasure (refineSignal P e) := Measure.isFiniteMeasure_map _ _
  have hb : (refineSignal P e).map (fun p => (p.1,p.2.1)) = P := by
    rw [refineSignal,Measure.map_map (measurable_fst.prodMk measurable_snd.fst)
      (measurable_fst.prodMk (measurable_snd.prodMk he))]
    exact Measure.map_id
  have hh := Measure.map_prod_map (refineSignal P e) (gaussianRows k d)
    (measurable_fst.prodMk measurable_snd.fst) measurable_id
  rw [Measure.map_id,hb] at hh
  exact hh.symm

lemma alignedExperiment_independent {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] :
    alignedExperiment (r:=r) (P.prod (gaussianRows m d)) = P.prod (gaussianRows (m+r) d) := by
  change (((P.prod (gaussianRows m d)).prod (gaussianRows r d)).map
    ((Prod.map id (fun p : Rows m d×Rows r d => Fin.append p.1 p.2)) ∘ MeasurableEquiv.prodAssoc)) = _
  rw [←Measure.map_map (measurable_id.prodMap (measurable_append (E:=Vector d) m r))
    MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod,
    ←Measure.map_prod_map _ _ measurable_id (measurable_append (E:=Vector d) m r),Measure.map_id]
  rw [show ((gaussianRows m d).prod (gaussianRows r d)).map (fun p => Fin.append p.1 p.2) =
    gaussianRows (m+r) d from map_append_pi (stdGaussian (Vector d)) m r]

lemma signal_marginal_of_independence {S W G : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] (P : Measure ((S×W)×G)) (ν : Measure S)
    (γ : Measure G) [IsProbabilityMeasure γ] [SFinite ν]
    (hInd : (P.map swapLast).fst = ν.prod γ) : P.fst.fst = ν := by
  have hh := congrArg Measure.fst hInd
  rw [Measure.fst_prod] at hh
  convert hh using 1
  simp only [Measure.fst,Measure.map_map measurable_fst measurable_fst,
    Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map measurable_fst (measurable_fst.comp swapLast.measurable)]
  rfl



end CurrentProjection

end

end OAI
