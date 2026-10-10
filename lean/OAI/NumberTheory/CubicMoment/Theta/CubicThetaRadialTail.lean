import OAI.NumberTheory.CubicMoment.Theta.CubicThetaL2Cutoff

namespace OAI

/-! The exponential cusp-tail estimate extends to the completed energy
space, using continuity of the actual L2 restriction operator. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaRadialJet_potential_norm {A : ℝ} (hA : 0 ≤ A)
    (f : ℝ → ℂ) (t : ℝ) :
    ‖cubicThetaRadialJet A f t 2‖^2=A*Real.exp (2*t)*‖f t‖^2 := by
  change ‖(Real.sqrt A*Real.exp t:ℝ) • f t‖^2=_
  rw [norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg A) (Real.exp_nonneg t))]
  have he : Real.exp (2*t)=(Real.exp t)^2 := by rw [two_mul,Real.exp_add]; ring
  rw [he]
  simp only [mul_pow,Real.sq_sqrt hA]

def cubicThetaRadialTail (A T : ℝ) :
    cubicThetaRadialEnergySpace A →L[ℂ] CubicThetaRadialL2 :=
  (cubicThetaL2Cutoff (Ioi T) measurableSet_Ioi).comp (cubicThetaRadialInclusion A)

lemma cubicThetaRadialTail_test_bound {A : ℝ} (hA : 0<A) (T : ℝ)
    (f : cubicThetaRadialTests) :
    ‖cubicThetaRadialTail A T (cubicThetaRadialEnergyTest A f)‖^2 ≤
      (A*Real.exp (2*T))⁻¹*‖cubicThetaRadialGraph A f‖^2 := by
  have hmass : ‖cubicThetaRadialCoordinate A 2 (cubicThetaRadialEnergyTest A f)‖^2=
      ∫ t : ℝ, A*Real.exp (2*t)*‖(f:ℝ → ℂ) t‖^2 := by
    rw [cubicTheta_l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [cubicThetaRadialCoordinate_test A 2 f] with t ht
    rw [ht,cubicThetaRadialJet_potential_norm hA.le]
  have htail : ‖cubicThetaRadialTail A T (cubicThetaRadialEnergyTest A f)‖^2=
      ∫ t in Ioi T, ‖(f:ℝ → ℂ) t‖^2 := by
    rw [cubicThetaRadialTail,ContinuousLinearMap.comp_apply,cubicThetaL2Cutoff_norm_sq]
    apply setIntegral_congr_ae measurableSet_Ioi
    filter_upwards [cubicThetaRadialInclusion_test A f] with t ht _
    rw [ht]
  rw [htail]
  calc
    _ ≤ (A*Real.exp (2*T))⁻¹*(∫ t : ℝ, A*Real.exp (2*t)*‖(f:ℝ → ℂ) t‖^2) :=
      cubicTheta_potential_tail f.property.1.continuous f.property.2.1 hA T
    _ = (A*Real.exp (2*T))⁻¹*‖cubicThetaRadialCoordinate A 2 (cubicThetaRadialEnergyTest A f)‖^2 := by rw [hmass]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (mul_nonneg hA.le (Real.exp_nonneg _)))
      have hb := cubicThetaRadialCoordinate_bound A 2 (cubicThetaRadialEnergyTest A f)
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) hb 2

theorem cubicThetaRadialTail_bound {A : ℝ} (hA : 0<A) (T : ℝ)
    (u : cubicThetaRadialEnergySpace A) :
    ‖cubicThetaRadialTail A T u‖^2 ≤ (A*Real.exp (2*T))⁻¹*‖u‖^2 := by
  let L : CubicThetaRadialAmbient →L[ℂ] CubicThetaRadialL2 :=
    (cubicThetaL2Cutoff (Ioi T) measurableSet_Ioi).comp
      ((cubicThetaRadialProjection 0).compLpL 2 volume)
  let S : Set CubicThetaRadialAmbient := {x | ‖L x‖^2 ≤ (A*Real.exp (2*T))⁻¹*‖x‖^2}
  have hc : IsClosed S := isClosed_le (L.continuous.norm.pow 2)
    (continuous_const.mul (continuous_norm.pow 2))
  have hs : ((cubicThetaRadialGraph A).range:Set CubicThetaRadialAmbient) ⊆ S := by
    rintro x ⟨f,rfl⟩
    exact cubicThetaRadialTail_test_bound hA T f
  exact closure_minimal hs hc u.property

end CubicFirstMoment

end

end OAI
