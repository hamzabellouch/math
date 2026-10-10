import Mathlib
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMapLipschitz
import OAI.Geometry.WeakHessian.LocalBounds.HopfInitialSlope

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile85
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [ProperSpace X] in
lemma integrable_density_slopeApprox_sq {u f : X → ℝ} (hu : Integrable u m)
    {L : ℝ≥0} (hf : LipschitzWith L f) (n : ℕ) :
    Integrable (fun x => u x*(slopeApprox f n x).toReal^2) m := by
  apply hu.mul_bdd ((lowerSemicontinuous_slopeApprox hf.continuous n).measurable.ennreal_toReal.pow_const 2).aestronglyMeasurable (c := (L:ℝ)^2)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq₀ ENNReal.toReal_nonneg L.coe_nonneg |>.mpr
    ((ENNReal.toReal_mono ENNReal.coe_ne_top (slopeApprox_le_lipschitz hf n x)).trans_eq (ENNReal.coe_toReal L))

omit [ProperSpace X] in
lemma tendsto_integral_slopeApprox {u f : X → ℝ} (hu : Integrable u m)
    {L : ℝ≥0} (hf : LipschitzWith L f) :
    Tendsto (fun n : ℕ => ∫ x,u x*(slopeApprox f n x).toReal^2 ∂m) atTop
      (𝓝 (∫ x,u x*(localSlope f x).toReal^2 ∂m)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖u x‖*(L:ℝ)^2)
  · intro n
    exact (integrable_density_slopeApprox_sq hu hf n).aestronglyMeasurable
  · exact hu.norm.mul_const _
  · intro n
    apply ae_of_all
    intro x
    rw [norm_mul,Real.norm_of_nonneg (sq_nonneg ((slopeApprox f n x).toReal))]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact sq_le_sq₀ ENNReal.toReal_nonneg L.coe_nonneg |>.mpr
      ((ENNReal.toReal_mono ENNReal.coe_ne_top (slopeApprox_le_lipschitz hf n x)).trans_eq (ENNReal.coe_toReal L))
  · exact ae_of_all _ fun x => ((tendsto_slopeApprox_toReal hf x).pow 2).const_mul (u x)

lemma integral_hopf_initial_eventually_lt (f : X →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    {u : X → ℝ} (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {a : ℝ} (ha : (∫ x,u x*(localSlope f x).toReal^2 ∂m)/2 < a) :
    ∀ᶠ s in 𝓝[>] (0:ℝ),(∫ x,u x*(f x-boundedHopfMap f s x) ∂m)/s < a := by
  obtain ⟨n,hn⟩ := ((tendsto_integral_slopeApprox hu hf).div_const 2).eventually_lt_const ha |>.exists
  have ht : Tendsto (fun s : ℝ => 2*s*(L:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (ht.const_mul 2).mul_const (L:ℝ)
  filter_upwards [ht.eventually_lt_const (by positivity : (0:ℝ) < 1/(n+1:ℝ)),self_mem_nhdsWithin] with s hs hs0
  apply lt_of_le_of_lt _ hn
  rw [← integral_div,← integral_div]
  apply integral_mono_ae
  · simpa only [BoundedContinuousFunction.sub_apply,div_eq_mul_inv,mul_assoc] using
      (integrable_bounded_pairing hu (f-boundedHopfMap f s)).mul_const s⁻¹
  · exact (integrable_density_slopeApprox_sq hu hf n).div_const 2
  · filter_upwards [hun] with x hx
    rw [boundedHopfMap_apply_pos f hs0,mul_div_assoc,mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hopf_initial_slopeApprox_bound f hf n x hs0 hs) hx
end WeakHessianTransport

end
end InlinedFile85

end OAI
