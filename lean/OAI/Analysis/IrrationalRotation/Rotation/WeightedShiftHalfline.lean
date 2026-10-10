import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftAlgebra

namespace OAI

noncomputable section
namespace Invariant233.WeightedShift

@[simp] theorem tailWeight_apply (m k : ℤ) :
    tailWeight m k = if m ≤ k then 1 else 0 := rfl

@[simp] theorem tailProjection_apply (m : ℤ) (ξ : Hilbert) (k : ℤ) :
    tailProjection m ξ k = if m ≤ k then ξ k else 0 := by
  change (if m ≤ k then (1 : ℂ) else 0) * ξ k = _
  split_ifs <;> simp

@[simp] theorem tailProjection_mul_self (m : ℤ) :
    tailProjection m * tailProjection m = tailProjection m := by
  ext ξ k
  simp only [mul_apply_eq_comp, tailProjection_apply]
  split_ifs <;> rfl

@[simp] theorem tailProjection_star (m : ℤ) :
    star (tailProjection m) = tailProjection m := by
  change star (diagonal (tailWeight m)) = diagonal (tailWeight m)
  rw [← diagonal_star]
  congr 1
  ext k
  simp only [lp.coeFn_star, Pi.star_apply, tailWeight_apply]
  split_ifs <;> simp

theorem isStarProjection_tailProjection (m : ℤ) :
    IsStarProjection (tailProjection m) :=
  ⟨tailProjection_mul_self m, tailProjection_star m⟩

theorem tailProjection_invariant (w : Weight) (m : ℤ) :
    (1 - tailProjection m) * operator w * tailProjection m = 0 := by
  ext ξ k
  change ((operator w (tailProjection m ξ)) k -
    (tailProjection m (operator w (tailProjection m ξ))) k) = 0
  by_cases hk : m ≤ k
  · simp [tailProjection_apply, hk]
  · have hk' : ¬ m ≤ k - 1 := by omega
    simp [tailProjection_apply, operator_apply, hk, hk']

theorem tailProjection_ne_zero (m : ℤ) : tailProjection m ≠ 0 := by
  intro h
  have he := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (lp.single 2 m 1) m) h
  simp at he

theorem tailProjection_ne_one (m : ℤ) : tailProjection m ≠ 1 := by
  intro h
  have he := congrArg
    (fun A : Hilbert →L[ℂ] Hilbert => A (lp.single 2 (m-1) 1) (m-1)) h
  have hm : ¬ m ≤ m - 1 := by omega
  simp [hm] at he

theorem tailProjection_not_covariant (m : ℤ) :
    (shift (-1)).toLinearIsometry.toContinuousLinearMap * tailProjection m *
      (shift 1).toLinearIsometry.toContinuousLinearMap ≠ tailProjection m := by
  rw [tailProjection, conjugate_diagonal]
  intro h
  have he := congrArg (fun w : Weight => w (m-1)) (diagonal_injective h)
  have hm : ¬ m ≤ m - 1 := by omega
  simp [translate_apply, hm] at he

end Invariant233.WeightedShift

end

end OAI
