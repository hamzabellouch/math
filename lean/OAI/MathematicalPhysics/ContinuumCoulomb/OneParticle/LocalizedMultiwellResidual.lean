import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedWellResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCorrectedOneBody
import Mathlib.Algebra.Order.Chebyshev

namespace OAI

/-! L2 bounds on the actual differential residuals of the localized modes.
The estimate is polynomial in the number of wells; it does not sum over a
many-electron occupation basis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def localizedMultiwellResidual (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) : ℝ :=
  ∑ k, if k = j then 0 else localizedWellAction freq (u j) (u k) x

theorem localizedMultiwellResidual_eq (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) :
    localizedMultiwellResidual freq u j x =
      multiwellAction freq u (localizedMode freq (u j)) (positionSplitCoordinates x) -
        ((-1/2 : ℝ)+freq/2)*continuumLocalizedMode freq (u j) x := by
  rw [show continuumLocalizedMode freq (u j) x =
    localizedMode freq (u j) (positionSplitCoordinates x) from rfl,
    multiwellAction_localizedMode]
  rfl

theorem localizedMultiwellResidual_memLp {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) :
    MemLp (localizedMultiwellResidual freq u j) 2 := by
  classical
  apply memLp_finsetSum
  intro k _
  by_cases hk : k = j
  · simp only [hk, ite_true]
    exact MemLp.zero
  · simp only [hk, ite_false]
    exact localizedWellAction_memLp hfreq _ _

theorem localizedMultiwellResidual_square_integrable {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) :
    Integrable (fun x => localizedMultiwellResidual freq u j x ^ 2) :=
  (localizedMultiwellResidual_memLp hfreq u j).integrable_sq

theorem localizedMultiwellResidual_square_bound {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (j : Fin m) :
    (∫ x, localizedMultiwellResidual freq u j x ^ 2) ≤
      (m : ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*
        Real.exp (-(19/10 : ℝ)*D) := by
  classical
  let f (k : Fin m) (x : Position) :=
    if k = j then 0 else localizedWellAction freq (u j) (u k) x
  have hi (k : Fin m) : Integrable (fun x => f k x ^ 2) := by
    by_cases hk : k = j
    · simp only [f, hk, ite_true, zero_pow (by norm_num : 2 ≠ 0)]
      exact integrable_zero Position ℝ volume
    · simpa only [f, hk, ite_false] using localizedWellAction_square_integrable hfreq (u j) (u k)
  have hpoint (x : Position) : localizedMultiwellResidual freq u j x ^ 2 ≤
      (m : ℝ)*(∑ k, f k x ^ 2) := by
    simpa only [localizedMultiwellResidual, f, Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => f k x))
  have h := integral_mono (localizedMultiwellResidual_square_integrable hfreq u j)
    ((integrable_finsetSum Finset.univ (fun k _ => hi k)).const_mul (m : ℝ)) hpoint
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun k _ => hi k)] at h
  have hterm (k : Fin m) : (∫ x, f k x ^ 2) ≤
      (PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10 : ℝ)*D) := by
    by_cases hk : k = j
    · simp only [f, hk, ite_true, zero_pow (by norm_num : 2 ≠ 0), integral_zero]
      exact mul_nonneg (mul_nonneg PlanarSobolev.wellBound_nonnegative
        planarWellMatrixConstant_nonnegative) (Real.exp_pos _).le
    · simpa only [f, hk, ite_false] using
        localizedWellAction_square_decay hfreq (u j) (u k) (hsep j k (Ne.symm hk))
  calc
    _ ≤ (m : ℝ)*(∑ k, ∫ x, f k x ^ 2) := h
    _ ≤ (m : ℝ)*(∑ _k : Fin m,
        (PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10 : ℝ)*D)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hterm k)) (Nat.cast_nonneg m)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end ContinuumCoulomb

end

end OAI
