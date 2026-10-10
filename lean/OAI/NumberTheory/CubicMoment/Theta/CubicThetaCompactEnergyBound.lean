import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCutoffEnergy

namespace OAI

/-! On a fixed compact subset of positive height, the hyperbolic
energy controls the Euclidean energy with one uniform constant. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaCompact_euclideanEnergy_bound {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : K⊆{y : ℂ × ℝ | 0<y.2}) :
    ∃ C≥0, ∀ (f : ℂ × ℝ → ℂ), tsupport f⊆K → ∀ y,
      ‖f y‖^2+cubicThetaFunctionEnergy f y≤C*‖cubicThetaLocalEnergyJet f y‖^2 := by
  obtain ⟨H₀,hH₀⟩ := hK.exists_bound_of_continuousOn continuous_snd.continuousOn
  let H := max H₀ 0
  have hH : 0≤H := le_max_right _ _
  have hC : 0≤H^3+H := add_nonneg (pow_nonneg hH _) hH
  refine ⟨H^3+H,hC,fun f hf y => ?_⟩
  by_cases hyK : y∈K
  · have hy : 0<y.2 := hpos hyK
    have hvH : y.2≤H := (le_abs_self _).trans ((hH₀ y hyK).trans (le_max_left _ _))
    have hv3 : y.2^3≤H^3 := by gcongr
    have hE : 0≤cubicThetaFunctionEnergy f y := cubicThetaTangentEnergy_nonneg _
    have hA := mul_le_mul_of_nonneg_right hv3 (sq_nonneg ‖f y‖)
    have hB := mul_le_mul_of_nonneg_right hvH (mul_nonneg (sq_nonneg y.2) hE)
    rw [cubicThetaLocalEnergyJet_density f hy,← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hy 3)).mpr
    nlinarith [mul_nonneg hH (sq_nonneg ‖f y‖),
      mul_nonneg (pow_nonneg hH 3) (mul_nonneg (sq_nonneg y.2) hE)]
  · have hyf : y∉tsupport f := fun hy => hyK (hf hy)
    have hz := image_eq_zero_of_notMem_tsupport hyf
    have hd := fderiv_of_notMem_tsupport (𝕜:=ℝ) hyf
    have hr := mul_nonneg hC (sq_nonneg ‖cubicThetaLocalEnergyJet f y‖)
    simpa only [hz,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
      cubicThetaFunctionEnergy,hd,ContinuousLinearMap.zero_comp,cubicThetaTangentEnergy,
      zero_apply,norm_zero,Finset.sum_const_zero,add_zero] using hr

end CubicFirstMoment

end

end OAI
