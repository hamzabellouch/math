import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialTail
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialGreen

namespace OAI

/-! The Green norm decreases with the actual Fourier potential. This
uniform estimate is needed when the cusp modes are assembled. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaRadialJet_mass_bound {A : ℝ} (hA : 0 ≤ A)
    (f : cubicThetaRadialTests) (t : ℝ) :
    (1+A)*‖(f:ℝ → ℂ) t‖^2 ≤ ‖cubicThetaRadialJet A f t‖^2 := by
  rw [cubicThetaRadialJet_norm_sq hA]
  by_cases ht : 0 ≤ t
  · have he : 1 ≤ Real.exp (2*t) := Real.one_le_exp_iff.mpr (by positivity)
    have hmul := mul_le_mul_of_nonneg_left he (mul_nonneg hA (sq_nonneg ‖(f:ℝ → ℂ) t‖))
    nlinarith [sq_nonneg ‖deriv (f:ℝ → ℂ) t‖]
  · rw [f.property.2.2 t (le_of_not_ge ht)]
    simp

lemma cubicThetaRadial_test_mass_bound {A : ℝ} (hA : 0 ≤ A) (f : cubicThetaRadialTests) :
    (1+A)*‖cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f)‖^2 ≤
      ‖cubicThetaRadialGraph A f‖^2 := by
  have hmass : ‖cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f)‖^2=
      ∫ t : ℝ, ‖(f:ℝ → ℂ) t‖^2 := by
    rw [cubicTheta_l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [cubicThetaRadialInclusion_test A f] with t ht
    rw [ht]
  have hjet : ‖cubicThetaRadialGraph A f‖^2=∫ t : ℝ, ‖cubicThetaRadialJet A f t‖^2 := by
    rw [cubicTheta_l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [(cubicThetaRadialJet_memLp A f).coeFn_toLp] with t ht
    change ‖((cubicThetaRadialJet_memLp A f).toLp _) t‖^2=_
    rw [ht]
  have hfLp : MemLp (f:ℝ → ℂ) 2 volume :=
    f.property.1.continuous.memLp_of_hasCompactSupport f.property.2.1
  have hfI := (memLp_two_iff_integrable_sq_norm hfLp.aestronglyMeasurable).mp hfLp
  have hjI := (memLp_two_iff_integrable_sq_norm
    (cubicThetaRadialJet_memLp A f).aestronglyMeasurable).mp (cubicThetaRadialJet_memLp A f)
  rw [hmass,hjet,← integral_const_mul]
  exact integral_mono_ae (hfI.const_mul _) hjI
    (ae_of_all _ (cubicThetaRadialJet_mass_bound hA f))

theorem cubicThetaRadial_mass_bound {A : ℝ} (hA : 0 ≤ A)
    (u : cubicThetaRadialEnergySpace A) :
    (1+A)*‖cubicThetaRadialInclusion A u‖^2 ≤ ‖u‖^2 := by
  let L := (cubicThetaRadialProjection 0).compLpL 2 (volume : Measure ℝ)
  let S : Set CubicThetaRadialAmbient := {x | (1+A)*‖L x‖^2 ≤ ‖x‖^2}
  have hc : IsClosed S := isClosed_le (continuous_const.mul (L.continuous.norm.pow 2))
    (continuous_norm.pow 2)
  have hs : ((cubicThetaRadialGraph A).range:Set CubicThetaRadialAmbient) ⊆ S := by
    rintro x ⟨f,rfl⟩
    exact cubicThetaRadial_test_mass_bound hA f
  exact closure_minimal hs hc u.property

theorem cubicThetaRadialGreen_conductor_bound {A : ℝ} (hA : 0 ≤ A) :
    ‖cubicThetaRadialGreen A‖ ≤ (1+A)⁻¹ := by
  have hpos : 0<1+A := by linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hpos.le)
  intro F
  by_cases hz : cubicThetaRadialGreen A F=0
  · rw [hz,_root_.norm_zero]
    positivity
  have hgpos : 0<‖cubicThetaRadialGreen A F‖ := norm_pos_iff.mpr hz
  have hmass := cubicThetaRadial_mass_bound hA (cubicThetaRadialWeakSolution A F)
  rw [← cubicThetaRadialGreen_apply,← cubicThetaRadialGreen_energy] at hmass
  have hinner : (inner ℂ F (cubicThetaRadialGreen A F)).re ≤
      ‖F‖*‖cubicThetaRadialGreen A F‖ := re_inner_le_norm (𝕜:=ℂ) F (cubicThetaRadialGreen A F)
  have hbound : (1+A)*‖cubicThetaRadialGreen A F‖ ≤ ‖F‖ := by
    nlinarith
  exact (le_inv_mul_iff₀ hpos).mpr hbound

end CubicFirstMoment

end

end OAI
