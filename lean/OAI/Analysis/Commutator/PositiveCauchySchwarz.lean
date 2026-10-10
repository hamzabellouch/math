import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sqrt_inner (A : H →L[ℂ] H) (ha : 0≤A) (x y : H) :
    inner ℂ (CFC.sqrt A x) (CFC.sqrt A y)=inner ℂ (A x) y := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A))
  have he := hs (CFC.sqrt A x) y
  have hh : CFC.sqrt A*CFC.sqrt A=A := by simpa only [pow_two] using CFC.sq_sqrt A ha
  change inner ℂ ((CFC.sqrt A*CFC.sqrt A) x) y=
    inner ℂ (CFC.sqrt A x) (CFC.sqrt A y) at he
  exact he.symm.trans (congrArg (fun T : H →L[ℂ] H => inner ℂ (T x) y) hh)

lemma sqrt_norm_sq (A : H →L[ℂ] H) (ha : 0≤A) (x : H) :
    ‖CFC.sqrt A x‖^2=(inner ℂ (A x) x).re := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),sqrt_inner A ha x x]
  rfl

lemma positive_cauchySchwarz (A : H →L[ℂ] H) (ha : 0≤A) (x y : H) :
    ‖inner ℂ (A x) y‖^2≤(inner ℂ (A x) x).re*(inner ℂ (A y) y).re := by
  have hh := norm_inner_le_norm (𝕜:=ℂ) (CFC.sqrt A x) (CFC.sqrt A y)
  have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hh
  rw [mul_pow,sqrt_norm_sq A ha x,sqrt_norm_sq A ha y,sqrt_inner A ha x y] at hs
  exact hs

lemma inverse_cauchySchwarz (A : (H →L[ℂ] H)ˣ) (ha : 0≤(A:H →L[ℂ] H)) (x y : H) :
    ‖inner ℂ x y‖^2≤(inner ℂ ((↑A⁻¹:H →L[ℂ] H) x) x).re*(inner ℂ ((A:H →L[ℂ] H) y) y).re := by
  have hh := positive_cauchySchwarz (A:H →L[ℂ] H) ha ((↑A⁻¹:H →L[ℂ] H) x) y
  have he : (A:H →L[ℂ] H) ((↑A⁻¹:H →L[ℂ] H) x)=x := by
    change ((A:H →L[ℂ] H)*(↑A⁻¹:H →L[ℂ] H)) x=x
    rw [Units.mul_inv,one_apply_eq_self]
  rw [he] at hh
  have hre : (inner ℂ x ((↑A⁻¹:H →L[ℂ] H) x)).re=
      (inner ℂ ((↑A⁻¹:H →L[ℂ] H) x) x).re := inner_re_symm (𝕜:=ℂ) _ _
  rw [hre] at hh
  exact hh

end Kadison.PositiveWOT

end

end
end

end OAI
