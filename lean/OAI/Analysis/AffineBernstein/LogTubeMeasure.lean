import Mathlib
import OAI.Analysis.AffineBernstein.TubeCompactIntegral
import OAI.Analysis.AffineBernstein.TubeCombination

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {k : ℕ} {μ : Measure (Space k)}

lemma measurable_logSpace : Measurable (logSpace : Space k → Space k) := by
  apply (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.measurable.comp
  exact Measurable.of_eval fun index =>
    Real.measurable_log.comp (EuclideanSpace.proj index).continuous.measurable

/- The actual logarithmic pushforward of a tube density, restricted to its
positive base domain. Only the nonnegative part outside that domain is discarded. -/
def logTubeMeasure (μ : Measure (Space k)) (D : Set (Space k)) (F : Space k × E → ℝ) :
    Measure (Space k) :=
  Measure.map (fun q : Space k × sphere (0:E) 1 => logSpace q.1)
    (((μ.prod (volume.toSphere : Measure (sphere (0:E) 1))).restrict
      (D ×ˢ Set.univ)).withDensity (fun q => ENNReal.ofReal (F (tubeLift q))))

lemma logPullback_zero_outside_domain {D : Set (Space k)} {φ : Space k → ℝ}
    (hDpos : D ⊆ positiveOrthant k) (hsupp : tsupport φ ⊆ logSpace '' D)
    {s : Space k} (hs : s ∉ D) : logPullback φ s = 0 := by
  by_cases hp : s ∈ positiveOrthant k
  · rw [logPullback_of_positive φ hp]
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    obtain ⟨y,hy,he⟩ := hsupp ht
    apply hs
    have heq : y = s := by
      have hh := congrArg expSpace he
      simpa only [expSpace_logSpace (hDpos hy),expSpace_logSpace hp] using hh
    simpa only [heq] using hy
  · exact ite_eq_right hp

lemma integral_logTubeMeasure {D : Set (Space k)} (hD : MeasurableSet D)
    (hDpos : D ⊆ positiveOrthant k) {F : Space k × E → ℝ}
    (hF : ContinuousOn F (tubeOpenSet D))
    (hFn : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ F (s,e))
    {φ : Space k → ℝ} (hφ : StronglyMeasurable φ)
    (hsupp : tsupport φ ⊆ logSpace '' D) :
    (∫ x, φ x ∂logTubeMeasure μ D F) =
      tubeIntegral μ F (logPullback φ) (fun _ => 1) := by
  have hP : MeasurableSet (D ×ˢ (Set.univ : Set (sphere (0:E) 1))) := hD.prod MeasurableSet.univ
  have hm : AEMeasurable (fun q : Space k × sphere (0:E) 1 => ENNReal.ofReal (F (tubeLift q)))
      ((μ.prod volume.toSphere).restrict (D ×ˢ Set.univ)) :=
    (hF.comp continuous_tubeLift.continuousOn (fun q hq => tubeLift_mem q hq.1)).aemeasurable hP |>.ennreal_ofReal
  have hmap : Measurable (fun q : Space k × sphere (0:E) 1 => logSpace q.1) :=
    measurable_logSpace.comp measurable_fst
  rw [logTubeMeasure,integral_map_of_stronglyMeasurable hmap hφ,
    integral_withDensity_eq_integral_toReal_smul₀ hm (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [← integral_indicator hP]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  by_cases hs : q.1 ∈ D
  · rw [Set.indicator_of_mem (show q ∈ D ×ˢ Set.univ from ⟨hs,Set.mem_univ _⟩)]
    simp only [tubeLift]
    rw [ENNReal.toReal_ofReal (hFn q.1 hs q.2 (mem_sphere_zero_iff_norm.1 q.2.property))]
    simp [logPullback_of_positive φ (hDpos hs)]
  · rw [Set.indicator_of_notMem (show q ∉ D ×ˢ Set.univ from fun h => hs h.1)]
    simp [logPullback_zero_outside_domain hDpos hsupp hs]

lemma integral_logTubeMeasure_mul {D : Set (Space k)} (hD : MeasurableSet D)
    (hDpos : D ⊆ positiveOrthant k) {M T : Space k × E → ℝ}
    (hM : ContinuousOn M (tubeOpenSet D)) (hT : ContinuousOn T (tubeOpenSet D))
    (hMn : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e))
    (hTn : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ T (s,e))
    {φ : Space k → ℝ} (hφ : StronglyMeasurable φ)
    (hsupp : tsupport φ ⊆ logSpace '' D) :
    (∫ x, φ x ∂logTubeMeasure μ D (fun q => M q*T q)) =
      tubeIntegral μ M (logPullback φ) T := by
  rw [integral_logTubeMeasure (μ := μ) (F := fun q => M q*T q) hD hDpos (hM.mul hT)
    (fun s hs e he => mul_nonneg (hMn s hs e he) (hTn s hs e he)) hφ hsupp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => by ring

lemma logPullback_sq (φ : Space k → ℝ) : logPullback (fun x => φ x^2) = fun s => logPullback φ s^2 := by
  funext s
  unfold logPullback
  split_ifs <;> simp

lemma logTubeMeasure_compact_lt_top [μ.IsAddHaarMeasure]
    {D : Set (Space k)} (hDpos : D ⊆ positiveOrthant k) {F : Space k × E → ℝ}
    (hF : ContinuousOn F (tubeOpenSet D))
    {K : Set (Space k)} (hK : IsCompact K) (hKD : K ⊆ logSpace '' D) :
    logTubeMeasure μ D F K < ⊤ := by
  have hmap : Measurable (fun q : Space k × sphere (0:E) 1 => logSpace q.1) :=
    measurable_logSpace.comp measurable_fst
  have hEK : IsCompact (expSpace '' K) := hK.image contDiff_expSpace.continuous
  have hED : expSpace '' K ⊆ D := by
    rintro s ⟨t,ht,rfl⟩
    obtain ⟨y,hy,rfl⟩ := hKD ht
    simpa only [expSpace_logSpace (hDpos hy)] using hy
  have hset : (fun q : Space k × sphere (0:E) 1 => logSpace q.1) ⁻¹' K ∩ (D ×ˢ Set.univ) =
      (expSpace '' K) ×ˢ Set.univ := by
    ext q
    constructor
    · rintro ⟨hq,hDq,-⟩
      exact ⟨⟨logSpace q.1,hq,expSpace_logSpace (hDpos hDq)⟩,Set.mem_univ _⟩
    · rintro ⟨⟨s,hs,he⟩,-⟩
      have ht : q.1 ∈ expSpace '' K := ⟨s,hs,he⟩
      refine ⟨?_,hED ht,Set.mem_univ _⟩
      change logSpace q.1 ∈ K
      rw [← he,logSpace_expSpace]
      exact hs
  rw [logTubeMeasure,Measure.map_apply hmap hK.measurableSet,
    withDensity_apply _ (hK.measurableSet.preimage hmap),
    Measure.restrict_restrict (hK.measurableSet.preimage hmap),hset]
  have hi : IntegrableOn (fun q : Space k × sphere (0:E) 1 => F (tubeLift q))
      ((expSpace '' K) ×ˢ Set.univ) (μ.prod volume.toSphere) :=
    ContinuousOn.integrableOn_compact (hEK.prod isCompact_univ)
      (hF.comp continuous_tubeLift.continuousOn (fun q hq => tubeLift_mem q (hED hq.1)))
  exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt hi.2

lemma integrable_logTubeMeasure [μ.IsAddHaarMeasure]
    {D : Set (Space k)} (hDpos : D ⊆ positiveOrthant k) {F : Space k × E → ℝ}
    (hF : ContinuousOn F (tubeOpenSet D)) {φ : Space k → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ logSpace '' D) :
    Integrable φ (logTubeMeasure μ D F) := by
  obtain ⟨C,hC⟩ := (hc.isCompact.image hφ).isBounded.exists_norm_le
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport φ)).mp
  exact IntegrableOn.of_bound (logTubeMeasure_compact_lt_top hDpos hF hc.isCompact hφD)
    hφ.aestronglyMeasurable C (ae_restrict_of_forall_mem hc.isCompact.measurableSet (fun x hx => hC (φ x) ⟨x,hx,rfl⟩))

end AffineBernstein
end

end OAI
