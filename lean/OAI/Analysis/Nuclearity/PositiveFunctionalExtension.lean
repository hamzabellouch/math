import OAI.Analysis.TracialSplitting.StateExtension

namespace OAI

/-! Positive functional extension along an injective unital star homomorphism,
including the zero functional. This is the scalar extension used in the
finite matrix extension construction. -/

noncomputable section
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem positiveFunctional_extension (ι : A →⋆ₐ[ℂ] B) (hι : Function.Injective ι)
    (f : A →ₚ[ℂ] ℂ) : ∃ g : B →ₚ[ℂ] ℂ, ∀ a, g (ι a) = f a := by
  let r := (f 1).re
  have hr : 0 ≤ r := (Complex.nonneg_iff.mp (f.map_nonneg zero_le_one)).1
  have hf1 : f 1 = (r : ℂ) := Complex.ext rfl
    (by simpa using (Complex.nonneg_iff.mp (f.map_nonneg zero_le_one)).2.symm)
  by_cases hz : r = 0
  · let g : B →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ 0 (by intro _ _; exact le_rfl)
    refine ⟨g, fun a => ?_⟩
    have hb := PositiveLinearMap.norm_map_star_mul_le f (1 : A) a
    simp only [star_one, one_mul, hf1, hz, Complex.ofReal_zero, norm_zero,
      Real.sqrt_zero, zero_mul] at hb
    have ha : f a = 0 := norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
    change 0 = f a
    exact ha.symm
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    let f₀ : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀
      ((r⁻¹ : ℂ) • f.toLinearMap) (by
        intro a ha
        change 0 ≤ (r⁻¹ : ℂ) * f a
        exact mul_nonneg (by exact_mod_cast (inv_nonneg.mpr hr)) (f.map_nonneg ha))
    have hf₀ : f₀ 1 = 1 := by
      change (r⁻¹ : ℂ) * f 1 = 1
      rw [hf1]
      exact_mod_cast inv_mul_cancel₀ hz
    obtain ⟨g₀, _, he⟩ := CurrentMain.state_extension ι hι f₀ hf₀
    let g : B →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ ((r : ℂ) • g₀.toLinearMap)
      (by intro b hb; exact mul_nonneg (by exact_mod_cast hr) (g₀.map_nonneg hb))
    refine ⟨g, fun a => ?_⟩
    change (r : ℂ) * g₀ (ι a) = f a
    rw [he]
    change (r : ℂ) * ((r⁻¹ : ℂ) * f a) = f a
    rw [← mul_assoc]
    rw [mul_inv_cancel₀ (show (r : ℂ) ≠ 0 by exact_mod_cast hz), one_mul]

end WeakPureInfiniteness

end

end OAI
