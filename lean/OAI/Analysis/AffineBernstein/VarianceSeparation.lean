import Mathlib
import OAI.Analysis.AffineBernstein.WeightedPoincare

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section VarianceSeparation

lemma variance_lower_of_separated_sets {n : ℕ} {K A B : Set (Space n)}
    (hK : IsCompact K) (hA : IsCompact A) (hB : IsCompact B)
    (hAK : A ⊆ K) (hBK : B ⊆ K) {f : Space n → ℝ} (hf : Continuous f)
    {L : ℝ} (hL : 0 ≤ L) (hsep : ∀ x ∈ A, ∀ y ∈ B, L ≤ f y-f x) :
    (volume A).toReal*(volume B).toReal*L^2 ≤
      ∫ x in K, ∫ y in K, (f y-f x)^2 := by
  let : IsFiniteMeasure (volume.restrict A) := ⟨by simpa using hA.measure_lt_top (μ := volume)⟩
  let : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hB.measure_lt_top (μ := volume)⟩
  let F := fun p : Space n × Space n => (f p.2-f p.1)^2
  have hF : Continuous F := by fun_prop
  have hFK := compact_integrable_pair (μ := volume) (ν := volume) hK hK hF
  have hFB := compact_integrable_pair (μ := volume) (ν := volume) hA hB hF
  have hFAK := compact_integrable_pair (μ := volume) (ν := volume) hA hK hF
  have hlo : (∫ x in A, ∫ y in B, L^2) ≤ ∫ x in A, ∫ y in B, F (x,y) := by
    apply setIntegral_mono_on (integrable_const _) hFB.integral_prod_left hA.measurableSet
    intro x hx
    apply setIntegral_mono_on (integrable_const _)
      (ContinuousOn.integrableOn_compact hB (hF.comp (continuous_const.prodMk continuous_id)).continuousOn)
      hB.measurableSet
    intro y hy
    exact (sq_le_sq₀ hL (hL.trans (hsep x hx y hy))).mpr (hsep x hx y hy)
  have hmid : (∫ x in A, ∫ y in B, F (x,y)) ≤ ∫ x in A, ∫ y in K, F (x,y) := by
    apply setIntegral_mono_on hFB.integral_prod_left hFAK.integral_prod_left hA.measurableSet
    intro point _
    apply setIntegral_mono_set
      (ContinuousOn.integrableOn_compact hK (hF.comp (continuous_const.prodMk continuous_id)).continuousOn)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall hBK)
  have hhi : (∫ x in A, ∫ y in K, F (x,y)) ≤ ∫ x in K, ∫ y in K, F (x,y) :=
    setIntegral_mono_set hFK.integral_prod_left
      (Filter.Eventually.of_forall (fun _ => MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)))
      (Filter.Eventually.of_forall hAK)
  have hh := hlo.trans (hmid.trans hhi)
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_assoc] using hh

lemma compact_sublevel_in_compact {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {f : Space n → ℝ} (hf : Continuous f) (t : ℝ) :
    IsCompact {x | x ∈ K ∧ f x ≤ t} :=
  hK.inter_right (isClosed_le hf continuous_const)

end VarianceSeparation


end
end AffineBernstein
end

end OAI
