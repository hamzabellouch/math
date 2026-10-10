import Mathlib
import OAI.Geometry.CAT0Fillings.Conformal.Closed

namespace OAI

section
open scoped RealInnerProductSpace

namespace CAT0Fillings.ChartGeometry

lemma chord_added_pointwise {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R V : E) (n β κ r u A f df : ℝ) (hn : n*β = 1+2*β) :
    κ^2*(n*(u^2*A^2*f)*‖R‖^2+
      r*inner ℝ R ((κ*u^2*A^3*df) • R+(u*A^2*((2+2*β)*f+β*(κ*r*A)*df)) • V)+
      inner ℝ V ((β*(2*r*u*A^2*f+κ*r^2*u*A^3*df)) • R+
        (β*r^2*A^2*((1+2*β)*f+β*(κ*r*A)*df)) • V)) =
      (n*f+(κ*r*A)*df)*‖(κ*u*A) • R+(κ*β*r*A) • V‖^2 := by
  rw [norm_add_sq_real]
  simp only [inner_add_right,real_inner_smul_right,real_inner_smul_left,
    real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  simp only [real_inner_comm V R]
  linear_combination (norm := (simp only [real_inner_comm V R]; ring)) -(κ^2*r*A^2*f*(2*u*inner ℝ R V+β*r*‖V‖^2))*hn

lemma profile_powers {u β : ℝ} (hu : 0 < u) :
    u^(1+β) = u*u^β ∧ u^(2+2*β) = u^2*(u^β)^2 ∧
    u^(2+3*β) = u^2*(u^β)^3 ∧ u^(1+2*β) = u*(u^β)^2 ∧
    u^(1+3*β) = u*(u^β)^3 ∧ u^(2*β) = (u^β)^2 := by
  have h2 : u^(2*β) = (u^β)^2 := by rw [←Real.rpow_mul_natCast hu.le]; congr 1; ring
  have h3 : u^(3*β) = (u^β)^3 := by rw [←Real.rpow_mul_natCast hu.le]; congr 1; ring
  simp only [Real.rpow_add hu,Real.rpow_one,Real.rpow_two,h2,h3,and_self]
end CAT0Fillings.ChartGeometry
end

section
open scoped RealInnerProductSpace

namespace CAT0Fillings.Conformal
lemma radial_profile_algebra {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R V : E) {n β κ r u : ℝ} (f : ℝ → ℝ) (hu : 0 < u) (hn : n*β = 1+2*β) :
    κ^2*(n*(u^(2+2*β)*f (κ*r*u^β))*‖R‖^2+
      r*inner ℝ R (profileRD 0 (2+2*β) β κ f r u • R+profileZD 0 (2+2*β) β κ f r u • V)+
      β*inner ℝ V (profileRD 2 (1+2*β) β κ f r u • R+profileZD 2 (1+2*β) β κ f r u • V)) =
      (n*f (κ*r*u^β)+(κ*r*u^β)*deriv f (κ*r*u^β))*
        ‖(κ*u^(1+β)) • R+(κ*β*r*u^β) • V‖^2 := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := ChartGeometry.profile_powers (β := β) hu
  have h7 : u^(3*β) = (u^β)^3 := by rw [←Real.rpow_mul_natCast hu.le]; congr 1; ring
  have hg : profileRD 0 (2+2*β) β κ f r u • R+profileZD 0 (2+2*β) β κ f r u • V =
      (κ*u^2*(u^β)^3*deriv f (κ*r*u^β)) • R+
      (u*(u^β)^2*((2+2*β)*f (κ*r*u^β)+β*(κ*r*u^β)*deriv f (κ*r*u^β))) • V := by
    simp only [profileRD,profileZD,Nat.cast_zero,pow_zero,zero_mul,zero_add,
      mul_one,show (2:ℝ)+2*β+β=2+3*β by ring,
      show (2:ℝ)+2*β-1=1+2*β by ring,show (2:ℝ)+3*β-1=1+3*β by ring,h3,h4,h5]
    congr 1 <;> congr 1 <;> ring
  have hp : β • (profileRD 2 (1+2*β) β κ f r u • R+profileZD 2 (1+2*β) β κ f r u • V) =
      (β*(2*r*u*(u^β)^2*f (κ*r*u^β)+κ*r^2*u*(u^β)^3*deriv f (κ*r*u^β))) • R+
      (β*r^2*(u^β)^2*((1+2*β)*f (κ*r*u^β)+β*(κ*r*u^β)*deriv f (κ*r*u^β))) • V := by
    simp only [profileRD,profileZD,Nat.cast_ofNat,show 2-1=(1:ℕ) by rfl,pow_one,
      show (1:ℝ)+2*β+β=1+3*β by ring,show (1:ℝ)+2*β-1=2*β by ring,
      show (1:ℝ)+3*β-1=3*β by ring,h4,h5,h6,h7,smul_add,smul_smul]
    congr 1 <;> congr 1 <;> ring
  rw [hg]
  have hi := real_inner_smul_right V
    (profileRD 2 (1+2*β) β κ f r u • R+profileZD 2 (1+2*β) β κ f r u • V) β
  rw [←hi,hp,h1,h2]
  simpa only [mul_assoc] using ChartGeometry.chord_added_pointwise R V n β κ r u (u^β)
    (f (κ*r*u^β)) (deriv f (κ*r*u^β)) hn
end CAT0Fillings.Conformal
end

end OAI
