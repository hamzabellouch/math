import OAI.NumberTheory.Ostmann.Characters.PivotResidueEquation
import OAI.NumberTheory.Ostmann.Characters.PivotResidueGrouping

namespace OAI

/-! # The grouped square has the actual transfer divisibility condition -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def pivotResidueKey (M : ℕ) [NeZero M] (L : ℕ) (v : ℤ) : Fin M :=
  (ZMod.finEquiv M).symm ((v : ZMod M) * (L : ZMod M)⁻¹)

theorem pivotResidueKey_eq_iff (M : ℕ) [NeZero M] (L R : ℕ)
    (hL : L.Coprime M) (hR : R.Coprime M) (v w : ℤ) :
    pivotResidueKey M L v = pivotResidueKey M R w ↔ (M : ℤ) ∣ v * R - w * L := by
  unfold pivotResidueKey
  rw [(ZMod.finEquiv M).symm.injective.eq_iff, pivot_residue_eq_iff M L R hL hR]

/-- The original coefficients are grouped inside the square before the
coprime residue condition is replaced by integer divisibility. -/
theorem pivot_square_expansion {A : Type*} [Fintype A]
    (M : ℕ) [NeZero M] (L : A → ℕ) (v : A → ℤ)
    (hL : ∀ a, (L a).Coprime M) (c : A → ℂ) :
    (∑ u : Fin M, ‖groupedCoefficient (fun a => pivotResidueKey M (L a) (v a)) c u‖ ^ 2) =
      (∑ a, ∑ b, if (M : ℤ) ∣ v a * L b - v b * L a then c a * conj (c b) else 0).re := by
  have h := diagonal_real_eq_sum_sq (fun a => pivotResidueKey M (L a) (v a)) c (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at h
  rw [← h]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [pivotResidueKey_eq_iff M (L a) (L b) (hL a) (hL b)]
  rfl

theorem pivot_zero_numerator_iff (L R : ℕ) (hLpos : 0 < L) (v w : ℤ)
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hL : ∀ q, q.Prime → q ∣ L → v.natAbs < q)
    (hR : ∀ q, q.Prime → q ∣ R → w.natAbs < q) :
    v * R - w * L = 0 ↔ L = R ∧ v = w := by
  constructor
  · intro h
    exact diagonal_products_equal L R hLpos v w hv hw (sub_eq_zero.mp h) hL hR
  · rintro ⟨rfl, rfl⟩
    simp

/-- The zero-numerator part is the exact equal-product/equal-frequency
square, including every ordered arrangement carrying that key. -/
theorem pivot_diagonal_expansion {A : Type*} [Fintype A]
    (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hLpos : ∀ a, 0 < L a) (hv : ∀ a, v a ≠ 0)
    (hlarge : ∀ a q, q.Prime → q ∣ L a → (v a).natAbs < q) :
    (∑ a, ∑ b, if v a * L b - v b * L a = 0 then c a * conj (c b) else 0) =
      ∑ a, ∑ b, if (L a, v a) = (L b, v b) then c a * conj (c b) else 0 := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [pivot_zero_numerator_iff (L a) (L b) (hLpos a) (v a) (v b) (hv a) (hv b)
    (hlarge a) (hlarge b), Prod.mk.injEq]

end Ostmann

end OAI
