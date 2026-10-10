import Mathlib
import OAI.Analysis.AffineBernstein.TubeCompactIntegral

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]

lemma integrable_tube_compactBase {K D : Set S} (hK : IsCompact K) (hKD : K ⊆ D)
    {f : S × E → ℝ} (hf : ContinuousOn f (tubeOpenSet D))
    (hz : ∀ s ∉ K, ∀ e : E, f (s,e) = 0) :
    Integrable (fun q : S × sphere (0:E) 1 => f (tubeLift q)) (μ.prod volume.toSphere) := by
  have hs : Function.support (fun q : S × sphere (0:E) 1 => f (tubeLift q)) ⊆
      K ×ˢ (Set.univ : Set (sphere (0:E) 1)) := by
    intro q hq
    refine ⟨?_,Set.mem_univ _⟩
    by_contra hn
    exact hq (hz q.1 hn q.2)
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact ContinuousOn.integrableOn_compact (hK.prod isCompact_univ)
    (hf.comp continuous_tubeLift.continuousOn (fun q hq => tubeLift_mem q (hKD hq.1)))

lemma tubeIntegral_supported_mono {K D : Set S} (hK : IsCompact K) (hKD : K ⊆ D)
    {M f g : S × E → ℝ} (hM : ContinuousOn M (tubeOpenSet D))
    (hf : ContinuousOn f (tubeOpenSet D)) (hg : ContinuousOn g (tubeOpenSet D))
    (hfz : ∀ s ∉ K, ∀ e : E, f (s,e) = 0) (hgz : ∀ s ∉ K, ∀ e : E, g (s,e) = 0)
    (hpos : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e))
    (hfg : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → f (s,e) ≤ g (s,e)) :
    tubeIntegral μ M (fun _ => 1) f ≤ tubeIntegral μ M (fun _ => 1) g := by
  simp only [tubeIntegral,mul_one]
  apply integral_mono_ae
    (integrable_tube_compactBase hK hKD (hM.mul hf) (fun s hs e => by simp [hfz s hs e]))
    (integrable_tube_compactBase hK hKD (hM.mul hg) (fun s hs e => by simp [hgz s hs e]))
  apply Filter.Eventually.of_forall
  intro q
  by_cases hs : q.1 ∈ K
  · exact mul_le_mul_of_nonneg_left (hfg q.1 (hKD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property))
      (hpos q.1 (hKD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property))
  · simp [tubeLift,hfz q.1 hs q.2,hgz q.1 hs q.2]

omit [NormedAddCommGroup S] [BorelSpace S] [μ.IsAddHaarMeasure] in
lemma tubeIntegral_supported_nonneg {K D : Set S} (hKD : K ⊆ D)
    {M f : S × E → ℝ} (hfz : ∀ s ∉ K, ∀ e : E, f (s,e) = 0)
    (hpos : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e) ∧ 0 ≤ f (s,e)) :
    0 ≤ tubeIntegral μ M (fun _ => 1) f := by
  apply integral_nonneg
  intro q
  by_cases hs : q.1 ∈ K
  · have hp := hpos q.1 (hKD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property)
    simpa [tubeLift] using mul_nonneg hp.1 hp.2
  · simp [tubeLift,hfz q.1 hs q.2]

end AffineBernstein
end

end OAI
