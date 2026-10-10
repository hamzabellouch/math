import OAI.Analysis.KadisonKastler.PublishedSimpleDerivation

namespace OAI

/-! # Bringing an ideal-extension implementer into the unital algebra

In Sakai's unital specialization, an implementer in an extension can
be multiplied by the original unit. If this product lies in the
original algebra, it implements the same derivation.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem inner_derivation_of_ideal_implementer
    (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ)
    (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (d : B) (hd : ∀ x, φ (D x) = d * φ x - φ x * d)
    (hunit : ∃ a : A, φ a = d * φ 1) :
    ∃ a : A, ∀ x, D x = a * x - x * a := by
  have hone : D 1 = 0 := by
    have h : D 1 + D 1 = D 1 + 0 := by
      simpa only [one_mul, mul_one, add_zero] using (hD 1 1).symm
    exact add_left_cancel h
  have hcomm : d * φ 1 = φ 1 * d := by
    have h := hd 1
    rw [hone, map_zero] at h
    exact sub_eq_zero.mp h.symm
  obtain ⟨a, ha⟩ := hunit
  refine ⟨a, fun x => hφ ?_⟩
  rw [hd, map_sub, map_mul, map_mul, ha]
  rw [mul_assoc, ← map_mul, one_mul]
  rw [hcomm, ← mul_assoc, ← map_mul, mul_one]

end

end KadisonKastler

end OAI
