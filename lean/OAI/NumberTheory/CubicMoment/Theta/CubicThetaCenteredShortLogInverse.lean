import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShortInverse
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShortLogInverse
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCenteredShortInverse

namespace OAI

/-! The centered short completion bound for logarithmic weights. -/
noncomputable section
namespace CubicFirstMoment

theorem LogarithmicWeightFamily.cubicTheta_centered_short_completion_error
    {ι : Type*} {Y : ι → ℝ} {W : ι → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W) (ℓ : ℤ)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, primary r → Squarefree r →
      ∀ U C : ℝ, (Y i)^(-B) ≤ U → U ≤ (Y i)^B →
      0 ≤ C → C ≤ (Y i)^B → norm r ≤ (Y i)^B →
      ‖metaplecticShortCompletionError r ℓ (W i) U C‖ ≤
        K*(Y i)^ε*Real.sqrt (norm r)*C^(3/2:ℝ) := by
  have hs : 0 < ε/2 := half_pos hε
  obtain ⟨K,hK,hbound⟩ := (hW.normalize hs).cubicTheta_centered_short_completion_error ℓ hs hB
  refine ⟨K,hK,?_⟩
  intro i r hr hsr U C hUlo hUhi hC hChi hrhi
  have hY : 0 < Y i := zero_lt_one.trans_le (hW.length_one i)
  have he : metaplecticShortCompletionError r ℓ (normalizedLogWeight Y W (ε/2) i) U C =
      (((Y i)^(-(ε/2)):ℝ):ℂ)*metaplecticShortCompletionError r ℓ (W i) U C := by
    change metaplecticShortCompletionError r ℓ (fun x => ((Y i)^(-(ε/2)):ℝ) • W i x) U C = _
    simp_rw [Complex.real_smul]
    exact metaplecticShortCompletionError_const_mul r ℓ (W i) U C _
  have hb := hbound i r hr hsr (Y i) U C (hW.length_one i) hUlo hUhi hC hChi hrhi
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hY.le _)] at hb
  have hp : (Y i)^(ε/2)*(Y i)^(-(ε/2)) = 1 := by
    rw [←Real.rpow_add hY,add_neg_cancel,Real.rpow_zero]
  calc
    _ = (Y i)^(ε/2)*((Y i)^(-(ε/2))*‖metaplecticShortCompletionError r ℓ (W i) U C‖) := by
      rw [←mul_assoc,hp,one_mul]
    _ ≤ (Y i)^(ε/2)*(K*(Y i)^(ε/2)*Real.sqrt (norm r)*C^(3/2:ℝ)) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)
    _ = K*((Y i)^(ε/2)*(Y i)^(ε/2))*Real.sqrt (norm r)*C^(3/2:ℝ) := by ring
    _ = _ := by rw [←Real.rpow_add hY,show ε/2+ε/2 = ε by ring]

end CubicFirstMoment

end

end OAI
