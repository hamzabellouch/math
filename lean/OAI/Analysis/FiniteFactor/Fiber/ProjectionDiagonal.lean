import OAI.Analysis.FiniteFactor.Fiber.Shift
import OAI.Analysis.FiniteFactor.CrossedProduct.FieldAlgebra

namespace OAI

namespace FiniteFactor
noncomputable section

/-- The diagonal of an orthogonal projection is the square norm of its column. -/
theorem fiberProjection_diagonal_inner (P : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hp : IsStarProjection P) (k : ℤ) :
    P (lp.single 2 k (1 : ℂ)) k =
      inner ℂ (P (lp.single 2 k (1 : ℂ))) (P (lp.single 2 k (1 : ℂ))) := by
  let e : SourceFiberHilbert := lp.single 2 k (1 : ℂ)
  have hi : P (P e) = P e := congrArg (fun A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert => A e)
    hp.isIdempotentElem
  calc
    _ = inner ℂ e (P e) := by simp [e,lp.inner_single_left]
    _ = inner ℂ e (star P (P e)) := by rw [hp.isSelfAdjoint.star_eq,hi]
    _ = _ := by rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

theorem fiberProjection_diagonal_zero_iff (P : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hp : IsStarProjection P) (k : ℤ) :
    P (lp.single 2 k (1 : ℂ)) k = 0 ↔ P (lp.single 2 k (1 : ℂ)) = 0 := by
  rw [fiberProjection_diagonal_inner P hp,inner_self_eq_zero]

theorem fiberProjection_diagonal_one_iff (P : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hp : IsStarProjection P) (k : ℤ) :
    P (lp.single 2 k (1 : ℂ)) k = 1 ↔ P (lp.single 2 k (1 : ℂ)) = lp.single 2 k (1 : ℂ) := by
  have he := fiberProjection_diagonal_zero_iff (1-P) hp.one_sub k
  change (lp.single 2 k (1 : ℂ) : SourceFiberHilbert) k - P (lp.single 2 k (1 : ℂ)) k = 0 ↔
    lp.single 2 k (1 : ℂ) - P (lp.single 2 k (1 : ℂ)) = 0 at he
  simp only [lp.single_apply,Pi.single_eq_same] at he
  rw [sub_eq_zero,sub_eq_zero] at he
  simpa only [eq_comm] using he

theorem fiberProjection_diagonal_bounds (P : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hp : IsStarProjection P) (k : ℤ) :
    0 ≤ (P (lp.single 2 k (1 : ℂ)) k).re ∧
    (P (lp.single 2 k (1 : ℂ)) k).re ≤ 1 ∧
    (P (lp.single 2 k (1 : ℂ)) k).im = 0 := by
  have hr : (P (lp.single 2 k (1 : ℂ)) k).re = ‖P (lp.single 2 k (1 : ℂ))‖ ^ 2 := by
    rw [fiberProjection_diagonal_inner P hp]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hb : 1 - (P (lp.single 2 k (1 : ℂ)) k).re = ‖(1-P) (lp.single 2 k (1 : ℂ))‖ ^ 2 := by
    have h := congrArg Complex.re (fiberProjection_diagonal_inner (1-P) hp.one_sub k)
    change ((lp.single 2 k (1 : ℂ) : SourceFiberHilbert) k - P (lp.single 2 k (1 : ℂ)) k).re = _ at h
    simpa only [lp.single_apply,Pi.single_eq_same,Complex.sub_re,Complex.one_re,
      show ∀ v : SourceFiberHilbert, (inner ℂ v v).re = ‖v‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ)] using h
  refine ⟨by rw [hr]; positivity,by nlinarith [sq_nonneg ‖(1-P) (lp.single 2 k (1 : ℂ))‖],?_⟩
  rw [fiberProjection_diagonal_inner P hp]
  exact inner_self_im (𝕜 := ℂ) _

/-- If a diagonal entry is zero, that coordinate annihilates the entire range. -/
theorem fiberProjection_range_coordinate_zero (P : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hp : IsStarProjection P) (k : ℤ) (hz : P (lp.single 2 k (1 : ℂ)) k = 0)
    (v : SourceFiberHilbert) : P v k = 0 := by
  have hzv := (fiberProjection_diagonal_zero_iff P hp k).mp hz
  have he : inner ℂ (lp.single 2 k (1 : ℂ)) (P v) =
      inner ℂ (P (lp.single 2 k (1 : ℂ))) v := by
    rw [← ContinuousLinearMap.adjoint_inner_right P (lp.single 2 k (1 : ℂ)) v,
      ← ContinuousLinearMap.star_eq_adjoint,hp.isSelfAdjoint.star_eq]
  simpa [lp.inner_single_left,hzv] using he

/-- Positivity of the diagonal weight transfers zero backwards and one forwards. -/
theorem fiberProjection_diagonal_implications
    (P Q D : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hp : IsStarProjection P) (hq : IsStarProjection Q)
    (hi : (1-Q)*D*P = 0) (a : ℂ) (ha : a ≠ 0)
    (hd : ∀ v : SourceFiberHilbert, D v 0 = a * v 0)
    (he : D (lp.single 2 0 (1 : ℂ)) = a • lp.single 2 0 (1 : ℂ)) :
    (Q (lp.single 2 0 (1 : ℂ)) 0 = 0 → P (lp.single 2 0 (1 : ℂ)) 0 = 0) ∧
    (P (lp.single 2 0 (1 : ℂ)) 0 = 1 → Q (lp.single 2 0 (1 : ℂ)) 0 = 1) := by
  let e : SourceFiberHilbert := lp.single 2 0 (1 : ℂ)
  have hfix : Q (D (P e)) = D (P e) := by
    have hh := congrArg (fun A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert => A e) hi
    change D (P e) - Q (D (P e)) = 0 at hh
    exact (sub_eq_zero.mp hh).symm
  constructor
  · intro hz
    have hcoord := congrArg (fun v : SourceFiberHilbert => v 0) hfix
    rw [fiberProjection_range_coordinate_zero Q hq 0 hz,hd] at hcoord
    exact (mul_eq_zero.mp hcoord.symm).resolve_left ha
  · intro h1
    have hpfix := (fiberProjection_diagonal_one_iff P hp 0).mp h1
    rw [hpfix,he,map_smul] at hfix
    have hqfix : Q e = e := (smul_right_injective _ ha) hfix
    exact (fiberProjection_diagonal_one_iff Q hq 0).mpr hqfix

end
end FiniteFactor

end OAI
