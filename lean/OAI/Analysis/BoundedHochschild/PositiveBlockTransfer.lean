import OAI.Analysis.BoundedHochschild.PositiveBlocks

namespace OAI

/-! A contraction respecting the scalar matrix actions preserves positive
two-by-two blocks with strictly positive scalar diagonal entries. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {D A B : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem positiveBlock_transfer_strict (ρ : D →⋆ₐ[ℂ] A) (σ : D →⋆ₐ[ℂ] B)
    (T : A →ₗ[ℂ] B) (hT : ∀ a, ‖T a‖ ≤ ‖a‖)
    (hmodule : ∀ d e a, T (ρ d * a * ρ e) = σ d * T a * σ e)
    (p q : D) (hp : IsStrictlyPositive p) (hq : IsStrictlyPositive q) (a : A)
    (ha : 0 ≤ positiveBlock (ρ p) (ρ q) a) :
    0 ≤ positiveBlock (σ p) (σ q) (T a) := by
  let u := p ^ (-(1 / 2) : ℝ)
  let v := q ^ (-(1 / 2) : ℝ)
  have hu := IsStrictlyPositive.rpow p (-(1 / 2) : ℝ) hp
  have hv := IsStrictlyPositive.rpow q (-(1 / 2) : ℝ) hq
  have hsu : star u = u := hu.nonneg.isSelfAdjoint.star_eq
  have hsv : star v = v := hv.nonneg.isSelfAdjoint.star_eq
  have hup : star u * p * u = 1 := by
    rw [hsu]
    exact CFC.conjugate_rpow_neg_one_half p hp
  have hvq : star v * q * v = 1 := by
    rw [hsv]
    exact CFC.conjugate_rpow_neg_one_half q hq
  have hρp : star (ρ u) * ρ p * ρ u = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg ρ hup
  have hρq : star (ρ v) * ρ q * ρ v = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg ρ hvq
  have hσp : star (σ u) * σ p * σ u = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg σ hup
  have hσq : star (σ v) * σ q * σ v = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg σ hvq
  have hρu : star (ρ u) = ρ u := by rw [← map_star, hsu]
  have hσu : star (σ u) = σ u := by rw [← map_star, hsu]
  have hnA : ‖ρ u * a * ρ v‖ ≤ 1 := by
    have h := star_left_conjugate_nonneg ha (diag (ρ u) (ρ v))
    rw [positiveBlock_conjugate, hρp, hρq, hρu, positiveBlock_one] at h
    exact norm_le_one_of_positiveUnitBlock _ h
  have hnB : ‖star (σ u) * T a * σ v‖ ≤ 1 := by
    rw [hσu, ← hmodule]
    exact (hT _).trans hnA
  have hpos := positiveUnitBlock_nonneg _ hnB
  have he := positiveBlock_conjugate (σ p) (σ q) (T a) (σ u) (σ v)
  rw [hσp, hσq, positiveBlock_one] at he
  rw [← he] at hpos
  exact (diag_isUnit (hu.isUnit.map σ.toMonoidHom) (hv.isUnit.map σ.toMonoidHom)).star_left_conjugate_nonneg_iff.mp hpos

end BoundedHochschild.KadisonRingrose

end

end OAI
