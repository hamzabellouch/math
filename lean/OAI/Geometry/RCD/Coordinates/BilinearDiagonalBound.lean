import OAI.Geometry.RCD.Sobolev.BochnerQuadraticBound

namespace OAI

/-! # A sharp mixed bound from diagonal bounds and a positive Gram form -/

noncomputable section
namespace RegularPointCoordinates

variable {m : ℕ}

/-- Diagonal domination of a symmetric form by a positive Gram form
controls its mixed entries, including when the Gram form is degenerate. -/
theorem bilinear_mixed_bound_of_diagonal
    (P H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ)
    (hP : ∀ a b, P a b=P b a) (hpos : ∀ a, 0≤P a a)
    (hH : ∀ a b, H a b=H b a) (C : ℝ) (hC : 0≤C)
    (hdiag : ∀ a, |H a a|≤C*P a a) (a b : Euclidean m) :
    (H a b)^2≤C^2*P a a*P b b := by
  let Q := C • P+H
  have hQ (x : Euclidean m) : 0≤Q x x := by
    change 0≤C*P x x+H x x
    have hx := (abs_le.mp (hdiag x)).1
    linarith only [hx]
  have hQsym (x y : Euclidean m) : Q x y=Q y x := by
    change C*P x y+H x y=C*P y x+H y x
    rw [hP,hH]
  have hzero (x y : Euclidean m) (hx : P x x=0) : H x y=0 := by
    have hp := finite_positive_bilinear_cauchySchwarz P hP hpos x y
    rw [hx,zero_mul] at hp
    have hxy : P x y=0 := by nlinarith only [hp,sq_nonneg (P x y)]
    have hxx : H x x=0 := by
      have hh := hdiag x
      rw [hx,mul_zero,abs_le] at hh
      linarith only [hh.1,hh.2]
    have hh := finite_positive_bilinear_cauchySchwarz Q hQsym hQ x y
    change (C*P x y+H x y)^2≤(C*P x x+H x x)*(C*P y y+H y y) at hh
    rw [hxy,hx,hxx] at hh
    nlinarith only [hh,sq_nonneg (H x y)]
  by_cases ha : P a a=0
  · rw [hzero a b ha,ha]
    simp
  by_cases hb : P b b=0
  · rw [hH a b,hzero b a hb,hb]
    simp
  have ha0 : 0<P a a := lt_of_le_of_ne (hpos a) (Ne.symm ha)
  have hb0 : 0<P b b := lt_of_le_of_ne (hpos b) (Ne.symm hb)
  let A := Real.sqrt (P b b)
  let B := Real.sqrt (P a a)
  have hA : A^2=P b b := Real.sq_sqrt (hpos b)
  have hB : B^2=P a a := Real.sq_sqrt (hpos a)
  have hplus := abs_le.mp (hdiag (A • a+B • b))
  have hminus := abs_le.mp (hdiag (A • a-B • b))
  simp only [map_add,map_sub,map_smul,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,smul_eq_mul] at hplus hminus
  rw [hP b a,hH b a] at hplus hminus
  ring_nf at hplus hminus
  rw [hA,hB] at hplus hminus
  have hbounds : -(C*P a a*P b b)≤A*B*H a b ∧ A*B*H a b≤C*P a a*P b b := by
    constructor <;> nlinarith only [hplus.1,hplus.2,hminus.1,hminus.2]
  have habs : |A*B*H a b|≤C*P a a*P b b := abs_le.mpr hbounds
  have hright : 0≤C*P a a*P b b := mul_nonneg (mul_nonneg hC (hpos a)) (hpos b)
  have hsq := (sq_le_sq₀ (abs_nonneg _) hright).mpr habs
  rw [sq_abs] at hsq
  have heq₁ : (A*B*H a b)^2=(P a a*P b b)*(H a b)^2 := by
    rw [mul_pow,mul_pow,hA,hB]
    ring
  have heq₂ : (C*P a a*P b b)^2=(P a a*P b b)*(C^2*P a a*P b b) := by ring
  rw [heq₁,heq₂] at hsq
  exact (mul_le_mul_iff_right₀ (mul_pos ha0 hb0)).mp hsq

/-- The square form of the diagonal estimate gives the same sharp mixed
estimate, with no division by the density or by a Gram eigenvalue. -/
theorem bilinear_mixed_sq_bound_of_diagonal
    (P H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ)
    (hP : ∀ a b, P a b=P b a) (hpos : ∀ a, 0≤P a a)
    (hH : ∀ a b, H a b=H b a) (B : ℝ) (hB : 0≤B)
    (hdiag : ∀ a, (H a a)^2≤B*(P a a)^2) (a b : Euclidean m) :
    (H a b)^2≤B*P a a*P b b := by
  have hroot : (Real.sqrt B)^2=B := Real.sq_sqrt hB
  have hbound (x : Euclidean m) : |H x x|≤Real.sqrt B*P x x := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg B) (hpos x))).mp
    rw [sq_abs,mul_pow,hroot]
    exact hdiag x
  simpa only [hroot] using bilinear_mixed_bound_of_diagonal P H hP hpos hH
    (Real.sqrt B) (Real.sqrt_nonneg B) hbound a b

end RegularPointCoordinates

end

end OAI
