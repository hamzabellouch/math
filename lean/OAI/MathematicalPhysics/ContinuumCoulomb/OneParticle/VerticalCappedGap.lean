import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalCutoffTail

namespace OAI

/-! The capped transverse oscillator inherits the published oscillator
projection bound, with a proved IMS cost and a proved Gaussian cutoff error. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem verticalCutoff_mass (S : ℝ) (u : ℝ → ℝ)
    (hu : Continuous u) (hc : HasCompactSupport u) :
    (∫ z, (verticalInnerCutoff S z*u z)^2) +
      (∫ z, (verticalOuterCutoff S z*u z)^2) = ∫ z, u z^2 := by
  have hci : HasCompactSupport (fun z => verticalInnerCutoff S z*u z) := hc.mul_left
  have hco : HasCompactSupport (fun z => verticalOuterCutoff S z*u z) := hc.mul_left
  have hsi : HasCompactSupport (fun z => (verticalInnerCutoff S z*u z)^2) :=
    hci.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hso : HasCompactSupport (fun z => (verticalOuterCutoff S z*u z)^2) :=
    hco.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hi : Integrable (fun z => (verticalInnerCutoff S z*u z)^2) :=
    (((verticalInnerCutoff_smooth S).continuous.mul hu).pow 2).integrable_of_hasCompactSupport hsi
  have ho : Integrable (fun z => (verticalOuterCutoff S z*u z)^2) :=
    (((verticalOuterCutoff_smooth S).continuous.mul hu).pow 2).integrable_of_hasCompactSupport hso
  rw [← integral_add hi ho]
  apply integral_congr_ae
  filter_upwards [] with z
  linear_combination u z^2 * verticalCutoff_partition S z

theorem verticalCappedForm_outer_lower {S : ℝ} (hS : 0 < S)
    (freq : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (freq^2*S^2/8) * (∫ z, (verticalOuterCutoff S z*u z)^2) ≤
      verticalCappedForm freq S (fun z => verticalOuterCutoff S z*u z) := by
  have ho : ContDiff ℝ 1 (fun z => verticalOuterCutoff S z*u z) :=
    ((verticalOuterCutoff_smooth S).of_le (by simp)).mul hu
  have hi := vertical_product_integrable (verticalCapPotential freq S) _
    (by unfold verticalCapPotential; fun_prop) ho.continuous hc.mul_left
  have hlo := vertical_product_integrable (fun _ => freq^2*S^2/8) _
    continuous_const ho.continuous hc.mul_left
  have hp : (∫ z, (freq^2*S^2/8)*(verticalOuterCutoff S z*u z)^2) ≤
      ∫ z, verticalCapPotential freq S z*(verticalOuterCutoff S z*u z)^2 := by
    apply integral_mono hlo hi
    intro z
    change (freq^2*S^2/8)*(verticalOuterCutoff S z*u z)^2 ≤
      verticalCapPotential freq S z*(verticalOuterCutoff S z*u z)^2
    by_cases hz : |z| ≤ S/2
    · rw [(verticalCutoff_inner hS hz).2]
      simp
    · have hs : S^2/4 ≤ z^2 := by
        have h := (sq_le_sq₀ (by positivity : 0 ≤ S/2) (abs_nonneg z)).mpr
          (le_of_not_ge hz)
        nlinarith [sq_abs z]
      have hm : S^2/4 ≤ min (z^2) (S^2) := le_min hs (by nlinarith [sq_nonneg S])
      have hv : freq^2*S^2/8 ≤ verticalCapPotential freq S z := by
        unfold verticalCapPotential
        nlinarith [mul_le_mul_of_nonneg_left hm (sq_nonneg freq)]
      exact mul_le_mul_of_nonneg_right hv (sq_nonneg _)
  rw [integral_const_mul] at hp
  unfold verticalCappedForm
  exact hp.trans (le_add_of_nonneg_left
    (mul_nonneg (by norm_num) (integral_nonneg (fun z => sq_nonneg _))))

/-- The only input is the published harmonic-oscillator gap. The slab
cutoff, exterior barrier and localization cost are explicit actual functions. -/
theorem verticalCappedForm_projection_lower (hpublished : PublishedVerticalOscillatorGap)
    {freq S : ℝ} (hfreq : 0 < freq) (hS : 0 < S)
    (hbarrier : 3*freq/2 ≤ freq^2*S^2/8)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (3*freq/2) * (∫ z, u z^2) -
      freq * (∫ z, (verticalInnerCutoff S z*u z)*verticalMode freq z)^2 -
      (verticalCutoffDerivativeBound S^2/2) * (∫ z, u z^2) ≤
      verticalCappedForm freq S u := by
  have hi : ContDiff ℝ 1 (fun z => verticalInnerCutoff S z*u z) :=
    ((verticalInnerCutoff_smooth S).of_le (by simp)).mul hu
  have hin := hpublished freq hfreq _ hi hc.mul_left
  rw [← verticalCappedForm_inner hS freq u] at hin
  have hout := (mul_le_mul_of_nonneg_right hbarrier
    (integral_nonneg (fun z => sq_nonneg (verticalOuterCutoff S z*u z)))).trans
      (verticalCappedForm_outer_lower hS freq u hu hc)
  have hm := verticalCutoff_mass S u hu.continuous hc
  have hims := verticalCappedForm_IMS freq S u hu hc
  have hcost : (∫ z, deriv (verticalCutoffAngle S) z^2*u z^2) ≤
      verticalCutoffDerivativeBound S^2 * (∫ z, u z^2) := by
    rw [← integral_const_mul]
    apply integral_mono
      (vertical_product_integrable _ u
        (((verticalCutoffAngle_smooth S).continuous_deriv (by simp)).pow 2) hu.continuous hc)
      (vertical_product_integrable _ u continuous_const hu.continuous hc)
    intro z
    change deriv (verticalCutoffAngle S) z^2*u z^2 ≤ verticalCutoffDerivativeBound S^2*u z^2
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hb := verticalCutoffAngle_deriv_bound hS z
    have hB : 0 ≤ verticalCutoffDerivativeBound S := by
      exact (abs_nonneg _).trans hb
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hb
  nlinarith

private theorem vertical_add_sq_le {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    (a+b)^2 ≤ (1+η)*a^2 + (1+η⁻¹)*b^2 := by
  have he : (((1+η)*a^2 + (1+η⁻¹)*b^2) - (a+b)^2)*η = (η*a-b)^2 := by
    field_simp [hη.ne']
    ring
  have hn : 0 ≤ (((1+η)*a^2 + (1+η⁻¹)*b^2) - (a+b)^2)*η := by
    rw [he]
    exact sq_nonneg _
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hn hη)

theorem verticalCutoff_pair_bound {freq S η : ℝ}
    (hfreq : 0 < freq) (hS : 0 < S) (hη : 0 < η)
    (u : ℝ → ℝ) (hu : MemLp u 2) :
    (∫ z, (verticalInnerCutoff S z*u z)*verticalMode freq z)^2 ≤
      (1+η)*(∫ z, u z*verticalMode freq z)^2 +
      (1+η⁻¹)*(∫ z, u z^2)*
        (verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)) := by
  have hy := vertical_add_sq_le hη (∫ z, u z*verticalMode freq z)
    ((∫ z, (verticalInnerCutoff S z*u z)*verticalMode freq z) -
      (∫ z, u z*verticalMode freq z))
  have he := mul_le_mul_of_nonneg_left (verticalCutoff_pair_error hfreq hS u hu)
    (show 0 ≤ 1+η⁻¹ by positivity)
  nlinarith

/-- The capped form has a global finite-rank lower bound. Unlike the
orthogonality corollary, this bound passes directly through approximation. -/
theorem verticalCappedForm_global_projection_lower
    (hpublished : PublishedVerticalOscillatorGap)
    {freq S η : ℝ} (hfreq : 0 < freq) (hS : 0 < S) (hη : 0 < η)
    (hbarrier : 3*freq/2 ≤ freq^2*S^2/8)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (3*freq/2 - verticalCutoffDerivativeBound S^2/2 -
      freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)) *
      (∫ z, u z^2) - freq*(1+η)*(∫ z, u z*verticalMode freq z)^2 ≤
        verticalCappedForm freq S u := by
  have h := verticalCappedForm_projection_lower hpublished hfreq hS hbarrier u hu hc
  have hp := verticalCutoff_pair_bound hfreq hS hη u
    (hu.continuous.memLp_of_hasCompactSupport hc)
  have hm := mul_le_mul_of_nonneg_left hp hfreq.le
  nlinarith

/-- Orthogonality is to the actual uncut Gaussian; its cutoff error is
accounted for quantitatively rather than inserted as a spectral premise. -/
theorem verticalCappedForm_complement_lower (hpublished : PublishedVerticalOscillatorGap)
    {freq S : ℝ} (hfreq : 0 < freq) (hS : 0 < S)
    (hbarrier : 3*freq/2 ≤ freq^2*S^2/8)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    (ho : (∫ z, u z*verticalMode freq z) = 0) :
    (3*freq/2 - verticalCutoffDerivativeBound S^2/2 -
      freq*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)) * (∫ z, u z^2) ≤
      verticalCappedForm freq S u := by
  have h := verticalCappedForm_projection_lower hpublished hfreq hS hbarrier u hu hc
  have hp := verticalCutoff_pair_error hfreq hS u
    (hu.continuous.memLp_of_hasCompactSupport hc)
  rw [ho, sub_zero] at hp
  have hm := mul_le_mul_of_nonneg_left hp hfreq.le
  nlinarith

end ContinuumCoulomb

end

end OAI
