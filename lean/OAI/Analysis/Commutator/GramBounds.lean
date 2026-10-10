import Mathlib
import OAI.Analysis.Commutator.FactorGeneratedSpace

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace CStarAlgebra

namespace Kadison.CbFactor

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma gram_boundedBelow (L : K →L[ℂ] H) (W : H →L[ℂ] K)
    (hLW : L.comp W=1) {c : ℝ} (hc : 0≤c) (hW : ‖W‖≤c) (x : H) :
    ‖x‖≤c^2*‖L (L.adjoint x)‖ := by
  have hadj := congrArg ContinuousLinearMap.adjoint hLW
  simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_one] at hadj
  have he : W.adjoint (L.adjoint x)=x := congrArg (fun T : H →L[ℂ] H => T x) hadj
  have hn : ‖x‖≤c*‖L.adjoint x‖ := by
    calc
      ‖x‖=‖W.adjoint (L.adjoint x)‖ := congrArg norm he.symm
      _ ≤ c*‖L.adjoint x‖ := (W.adjoint.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (by simpa using hW) (norm_nonneg _))
  have hi : ‖L.adjoint x‖^2=(inner ℂ x (L (L.adjoint x))).re := by
    rw [←ContinuousLinearMap.adjoint_inner_left,inner_self_eq_norm_sq_to_K]
    simp [←Complex.ofReal_pow]
  have hh : (inner ℂ x (L (L.adjoint x))).re≤‖x‖*‖L (L.adjoint x)‖ := re_inner_le_norm (𝕜:=ℂ) _ _
  have hs := pow_le_pow_left₀ (norm_nonneg x) hn 2
  rw [mul_pow,hi] at hs
  have hmul := mul_le_mul_of_nonneg_left hh (pow_nonneg hc 2)
  by_cases hx : ‖x‖=0
  · rw [hx]; positivity
  · have hx0 : 0<‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    nlinarith

lemma gram_inverse_norm_le (L : K →L[ℂ] H) (W : H →L[ℂ] K)
    (hLW : L.comp W=1) {c : ℝ} (hc : 0≤c) (hW : ‖W‖≤c)
    (u : (H →L[ℂ] H)ˣ) (hu : (u : H →L[ℂ] H)=L.comp L.adjoint) :
    ‖(↑(u⁻¹) : H →L[ℂ] H)‖≤c^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg c)
  intro x
  have h := gram_boundedBelow L W hLW hc hW ((↑(u⁻¹) : H →L[ℂ] H) x)
  have he : L (L.adjoint ((↑(u⁻¹) : H →L[ℂ] H) x))=x := by
    change ((L.comp L.adjoint)*(↑(u⁻¹) : H →L[ℂ] H)) x=x
    rw [←hu,Units.mul_inv]
    rfl
  simpa only [he] using h

variable {A : Type*} [CStarAlgebra A]

lemma leftCompression_norm_le (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (V W : H →L[ℂ] K)
    (hV : ‖V‖≤1) : ‖leftCompression ρ V W‖≤1 := by
  unfold leftCompression
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hp : ‖(generated ρ W).starProjection‖≤1 := Submodule.starProjection_norm_le _
  exact (mul_le_mul (by simpa using hV) hp (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end Kadison.CbFactor

end

end
end

end OAI
