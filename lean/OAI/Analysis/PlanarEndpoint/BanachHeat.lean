import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphTree
import OAI.Analysis.PlanarEndpoint.Heat

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal
namespace PlanarEndpoint

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

omit [NormedSpace ℝ B] [CompleteSpace B] in
lemma locallyIntegrable_reflect_banach {U : Plane → B}
    (hU : LocallyIntegrable U volume) (x : Plane) :
    LocallyIntegrable (fun z => U (x-z)) volume := by
  intro y
  refine ⟨ball y 1, ball_mem_nhds y zero_lt_one, ?_⟩
  have hi := (hU.integrableOn_isCompact (isCompact_closedBall (x-y) 1)).mono_set
    ball_subset_closedBall
  have hm := (volume.measurePreserving_sub_left x).restrict_preimage
    (measurableSet_ball (x := x-y) (ε := (1 : ℝ)))
  have hh := (hm.integrable_comp hi.aestronglyMeasurable).mpr hi
  simpa only [IntegrableOn, Function.comp_def, reflect_preimage_ball, sub_sub_cancel] using hh

omit [NormedSpace ℝ B] [CompleteSpace B] in
lemma locallyIntegrable_norm {U : Plane → B} (hU : LocallyIntegrable U volume) :
    LocallyIntegrable (fun y => ‖U y‖) volume := by
  rw [← locallyIntegrableOn_univ]
  exact (hU.locallyIntegrableOn univ).norm

omit [NormedSpace ℝ B] [CompleteSpace B] in
lemma diskNormAverage_eq_average_banach (U : Plane → B) (x : Plane) (z : B)
    {r : ℝ} (hr : 0 ≤ r) :
    (Real.pi * r ^ 2)⁻¹ * (∫ y in ball x r, ‖U y - z‖) =
      ⨍ y in closedBall x r, ‖U y - z‖ := by
  rw [setAverage_congr (closedBall_ae_eq_ball x r), setAverage_eq]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_nonneg,
    smul_eq_mul]
  rw [mul_comm (r ^ 2) Real.pi]

omit [NormedSpace ℝ B] [CompleteSpace B] in
lemma ae_banachLebesguePoint {U : Plane → B} (hU : LocallyIntegrable U volume) :
    ∀ᵐ x : Plane ∂volume, Tendsto (fun r : ℝ => (Real.pi*r^2)⁻¹ *
      ∫ y in ball x r, ‖U y-U x‖) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hU 1] with x hx
  have hc : ∀ᶠ r : ℝ in 𝓝[>] 0, x ∈ closedBall x (1*r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [one_mul, mem_closedBall, dist_self] using (le_of_lt hr)
  have ht := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id hc
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (diskNormAverage_eq_average_banach U x (U x) (le_of_lt hr)).symm

omit [NormedSpace ℝ B] [CompleteSpace B] in
lemma integral_norm_sub_unit_ball_le {U : Plane → B} (hU : LocallyIntegrable U volume)
    {A : ℝ} (hball : ∀ x : Plane, ∫ y in ball x 1, ‖U y‖ ≤ A) (x c : Plane) :
    ∫ y in ball c 1, ‖U y-U x‖ ≤ A + Real.pi * ‖U x‖ := by
  have hi := (hU.integrableOn_isCompact (isCompact_closedBall c 1)).mono_set ball_subset_closedBall
  have hc : IntegrableOn (fun _ : Plane => U x) (ball c 1) volume := integrableOn_const
  calc
    _ ≤ ∫ y in ball c 1, ‖U y‖ + ‖U x‖ := integral_mono (hi.sub hc).norm
      (hi.norm.add hc.norm) (fun y => norm_sub_le _ _)
    _ = (∫ y in ball c 1, ‖U y‖) + Real.pi * ‖U x‖ := by
      rw [integral_add hi.norm hc.norm, setIntegral_const]
      simp [measureReal_def, EuclideanSpace.volume_ball_fin_two, Real.pi_nonneg, smul_eq_mul]
    _ ≤ _ := add_le_add (hball c) le_rfl

omit [CompleteSpace B] in
lemma integrable_heat_smul {U : Plane → B} (hU : LocallyIntegrable U volume)
    (A : ℝ≥0) (hball : ∀ x : Plane, ∫ y in ball x 1, ‖U y‖ ≤ A)
    {a : ℝ} (ha : 0 < a) (x : Plane) :
    Integrable (fun z => heatKernel a z • U (x-z)) volume := by
  have hh := (heat_envelope (locallyIntegrable_norm hU) (fun y => norm_nonneg _) A hball x).1 a ha
  apply hh.mono'
  · exact (by unfold heatKernel gaussianWeight; fun_prop : Continuous (heatKernel a)).aestronglyMeasurable.smul
      (locallyIntegrable_reflect_banach hU x).aestronglyMeasurable
  · filter_upwards [] with z
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ha.le z), le_refl]

lemma tendsto_heat_smul_of_lebesgue {U : Plane → B} (hU : LocallyIntegrable U volume)
    (A : ℝ≥0) (hball : ∀ x : Plane, ∫ y in ball x 1, ‖U y‖ ≤ A) (x : Plane)
    (hLeb : Tendsto (fun r : ℝ => (Real.pi*r^2)⁻¹ * ∫ y in ball x r, ‖U y-U x‖)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun a : ℝ => ∫ z, heatKernel a z • U (x-z)) (𝓝[>] 0) (𝓝 (U x)) := by
  let h : Plane → ℝ := fun y => ‖U y-U x‖
  have hl : LocallyIntegrable h volume :=
    locallyIntegrable_norm (hU.sub (locallyIntegrable_const (U x)))
  let A' : ℝ≥0 := A + ⟨Real.pi * ‖U x‖, mul_nonneg Real.pi_nonneg (norm_nonneg _)⟩
  have hb : ∀ c : Plane, ∫ y in ball c 1, h y ≤ A' :=
    integral_norm_sub_unit_ball_le hU hball x
  have hh := (heat_envelope hl (fun y => norm_nonneg _) A' hb x).2
  have hlim : Tendsto (fun a : ℝ => ∫ z, heatKernel a z * h (x-z)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [h, sub_self, norm_zero, sub_zero, abs_norm] using
      hh (by simpa only [h, sub_self, norm_zero, sub_zero, abs_norm] using hLeb)
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [self_mem_nhdsWithin, hlim.eventually (eventually_lt_nhds hε)] with a ha he
  have hi := integrable_heat_smul hU A hball ha x
  have hc := (integrable_heatKernel ha).smul_const (U x)
  have heq : (∫ z, heatKernel a z • U (x-z)) - U x =
      ∫ z, heatKernel a z • (U (x-z)-U x) := by
    simp_rw [smul_sub]
    rw [integral_sub hi hc, integral_smul_const, integral_heatKernel ha, one_smul]
  rw [dist_eq_norm, heq]
  calc
    _ ≤ ∫ z, ‖heatKernel a z • (U (x-z)-U x)‖ := norm_integral_le_integral_norm _
    _ = ∫ z, heatKernel a z * h (x-z) := by
      congr 1
      ext z
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ha.le z)]
    _ < ε := he

end PlanarEndpoint
end

end OAI
