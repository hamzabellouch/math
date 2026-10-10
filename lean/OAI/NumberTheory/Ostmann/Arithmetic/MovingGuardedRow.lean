import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeRowNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularTransfer

namespace OAI

/-! # The extracted row with the original support indicators -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingGuardedRow {J : Type*} [Fintype J]
    (q : J → ℕ) (g : ∀ j, ZMod (q j) → ℂ) (D : ℕ) {M : ℕ} (t : Fin M) : ℂ :=
  if Pairwise (fun i j => (q i).Coprime (q j)) ∧ (∀ j, D.Coprime (q j)) then
    ∏ j, g j ((t.val : ZMod (q j)) * ((D * tupleCofactor q j : ℕ) : ZMod (q j))⁻¹)
  else 0

/-- Invalid compensation vectors stay in the original sample space with
zero row. No conditioning or renormalization of that sample law is used. -/
theorem movingGuardedRow_energy {J : Type*} [Fintype J]
    (q : J → ℕ) [∀ j, Fact (q j).Prime]
    (g : ∀ j, ZMod (q j) → ℂ) (D M : ℕ) (hM : (∏ j, q j) = M)
    (giant : J) (S : ∀ j, Finset (ZMod (q j)))
    (hg : ∀ x, ‖g giant x‖ ≤ 1)
    (hregular : ∀ j, j ≠ giant → g j = normalizedResidueTransform (S j))
    (hS : ∀ j, j ≠ giant → (S j).Nonempty)
    (hSp : ∀ j, j ≠ giant → (S j).card < q j) :
    (∑ t : Fin M, ‖movingGuardedRow q g D t‖ ^ 2) ≤ M := by
  by_cases h : Pairwise (fun i j => (q i).Coprime (q j)) ∧ (∀ j, D.Coprime (q j))
  · let : NeZero (∏ j, q j) := ⟨(Finset.prod_pos (fun j _ => (Fact.out : (q j).Prime).pos)).ne'⟩
    have he := moving_compensation_fourier_row_energy q h.1 giant g S hg hregular hS hSp D h.2
    rw [hM] at he
    simpa only [movingGuardedRow, ite_eq_left h, div_eq_mul_inv] using he
  · simp only [movingGuardedRow, ite_eq_right h, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, Nat.cast_nonneg]

/-- On support this is exactly the current transform at the grouped key. -/
theorem movingGuardedRow_grouped {J : Type*} [Fintype J]
    (q : J → ℕ) [∀ j, Fact (q j).Prime]
    (g : ∀ j, ZMod (q j) → ℂ) (D H : ℕ) (v : ℤ)
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) (hD : ∀ j, D.Coprime (q j))
    (hH : H.Coprime (∏ j, q j)) :
    movingGuardedRow q g D (positiveIntegerPivotKey (∏ j, q j)
      (Finset.prod_pos (fun j _ => (Fact.out : (q j).Prime).pos)) H v) =
      movingRegularTransform q g (D * H) v := by
  rw [movingGuardedRow, ite_eq_left ⟨hc, hD⟩]
  have he := moving_regular_transform_grouped_key q g H D v hH
  simpa only [movingRegularTransform, Int.cast_natCast] using he

end Ostmann

end OAI
