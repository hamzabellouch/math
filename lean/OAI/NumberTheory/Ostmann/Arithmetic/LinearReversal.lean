import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.LinearReversal

variable {K : Type*} [Field K]

def leftStep (a b : K) (hb : b ≠ 0) : (K × K) ≃ₗ[K] (K × K) where
  toFun z := (a*z.1+b*z.2,z.1)
  invFun z := (z.2,(z.1-a*z.2)/b)
  left_inv z := by
    apply Prod.ext
    · rfl
    · dsimp
      field_simp
      ring
  right_inv z := by
    apply Prod.ext
    · dsimp
      field_simp
      ring
    · rfl
  map_add' z w := by ext <;> dsimp; ring
  map_smul' c z := by ext <;> dsimp; ring

def rightStep (a b : K) (ha : a ≠ 0) : (K × K) ≃ₗ[K] (K × K) where
  toFun z := (a*z.1+b*z.2,z.2)
  invFun z := ((z.1-b*z.2)/a,z.2)
  left_inv z := by
    apply Prod.ext
    · dsimp
      field_simp
      ring
    · rfl
  right_inv z := by
    apply Prod.ext
    · dsimp
      field_simp
      ring
    · rfl
  map_add' z w := by ext <;> dsimp; ring
  map_smul' c z := by ext <;> dsimp; ring

theorem pivot_linear {v w Cp Cm s u p Xp Xm : K}
    (hs : s ≠ 0) (hu : u ≠ 0)
    (h : v*(Xm*Cm)-w*(Xp*Cp)=s*u*p) :
    p = (-w*Cp/(s*u))*Xp+(v*Cm/(s*u))*Xm := by
  field_simp
  linear_combination -h

theorem nonzero_form_comp (e : (K × K) ≃ₗ[K] (K × K)) (a b : K)
    (h : a ≠ 0 ∨ b ≠ 0) :
    ¬ ∀ z : K × K, a*(e z).1+b*(e z).2=0 := by
  intro hz
  have h₁ := hz (e.symm (1,0))
  have h₂ := hz (e.symm (0,1))
  simp only [e.apply_symm_apply,mul_one,mul_zero,add_zero,zero_add] at h₁ h₂
  exact h.elim (fun ha => ha h₁) (fun hb => hb h₂)

theorem left_row_coefficients (a b c d x y : K) :
    c*(a*x+b*y)+d*x=(c*a+d)*x+(c*b)*y := by ring

theorem right_row_coefficients (a b c d x y : K) :
    c*(a*x+b*y)+d*y=(c*a)*x+(c*b+d)*y := by ring

end Ostmann.Arithmetic.LinearReversal

end

end OAI
