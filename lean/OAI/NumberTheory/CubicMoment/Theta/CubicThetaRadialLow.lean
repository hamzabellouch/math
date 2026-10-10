import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialRawVoronoi
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompletedLow

namespace OAI

/-! Uniform low-height bounds after subtracting the actual radial residue.
The normalization of that residue is not needed for this remainder bound. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem uniform_cubicTheta_radial_remainder_low
    {ι : Type*} {W : ι→ℝ→ℂ} (hW : UniformLogWeights W)
    {ε σ : ℝ} (hε : 0<ε) (hσ : 0<σ) :
    ∃ K : ℝ, 0≤K ∧ ∀ i r, primary r → Squarefree r → ∀ X : ℝ, 0<X →
      ‖metaplecticCompleted r 0 (W i) X-cubicThetaActualCompletedRadialMain r (W i) X‖≤
        K*Real.sqrt (norm r)*norm r^(ε+2*σ)*X^(-σ) := by
  have hGamma := angularGammaQuotientStripBound_proved (metaplecticAngularShift 0)
    (-σ-1/6) (lt_of_lt_of_le (by norm_num : -(1/2:ℝ)<0) (metaplecticAngularShift_nonneg 0))
  obtain ⟨C,hC,hTr⟩ := hW.metaplecticTransform_bound 0 hσ hGamma
  obtain ⟨M,hM,hMass⟩ := metaplectic_coefficient_mass_small_power
    cubicThetaCoreCoefficient_bounds hε hσ
  let S : ℝ := ∑' d : PrimaryArgument,norm d^(-5/2-3*σ)
  have hS : 0≤S := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  let P : ℝ := 3^(7/2:ℝ)*(2*Real.pi)^2
  have hP : 0<P := by dsimp [P]; positivity
  refine ⟨81*C*M*S*(2*Real.pi)^(-4*σ)*(729:ℝ)^σ/P,by positivity,?_⟩
  intro i r hr hsr X hX
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hRs : norm r^(2*σ)*norm r^ε=norm r^(ε+2*σ) := by
    rw [←Real.rpow_add hR]
    congr 1
    ring
  have hbound := metaplecticDualTerm_tsum_norm_bound hr 0 (W i) hσ
    (div_pos hX (by norm_num : (0:ℝ)<729)) hC (hTr i)
    (hMass r hr hsr).1 (hMass r hr hsr).2
  rw [cubicTheta_completed_radial_voronoi hr hsr (W i) (hW.compact i)
    (hW.positive i) (hW.smooth i) hσ hX,add_sub_cancel_right,norm_mul,norm_mul,
    norm_metaplecticPrefactor (primary_ne_zero hr),Complex.norm_ofNat]
  calc
    _ ≤ (81*(Real.sqrt (norm r)/P))*
        ((C*((2*Real.pi)^(-4*σ)*(X/729)^(-σ)*norm r^(2*σ)))*(M*norm r^ε)*S) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (81*C*M*S*(2*Real.pi)^(-4*σ)*(729:ℝ)^σ/P)*Real.sqrt (norm r)*
        (norm r^(2*σ)*norm r^ε)*X^(-σ) := by rw [cubicTheta_dilated_power hX]; ring
    _ = _ := by rw [hRs]

end CubicFirstMoment

end

end OAI
