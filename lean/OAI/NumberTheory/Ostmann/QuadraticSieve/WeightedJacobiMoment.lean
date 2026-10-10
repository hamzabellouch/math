import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import OAI.NumberTheory.Ostmann.Characters.SquareProductMoment

namespace OAI

/-! # Transferring square-product moments to weighted Jacobi sums

The nonsquare error is an explicit numerical bound to be supplied by the
periodic-character calculation; it is not a published or global assumption.
-/

namespace Ostmann

open scoped BigOperators

def realJacobi (n m : ℕ) : ℝ := (jacobiSym (n : ℤ) m : ℝ)

theorem realJacobi_abs_le (n m : ℕ) : |realJacobi n m| ≤ 1 := by
  rcases jacobiSym.trichotomy (n : ℤ) m with h | h | h <;> simp [realJacobi, h]

theorem realJacobi_prod {ι : Type*} (S : Finset ι) (s : ι → ℕ) (m : ℕ) :
    realJacobi (∏ i ∈ S, s i) m = ∏ i ∈ S, realJacobi (s i) m := by
  let J : ℕ →* ℝ :=
    { toFun := fun n => realJacobi n m
      map_one' := by simp [realJacobi, jacobiSym.one_left]
      map_mul' := fun a b => by simp [realJacobi, jacobiSym.mul_left] }
  exact map_prod J s S

theorem weighted_jacobi_abs_le_mass (T : Finset ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ m ∈ T, 0 ≤ μ m) (n : ℕ) :
    |∑ m ∈ T, μ m * realJacobi n m| ≤ ∑ m ∈ T, μ m := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  rw [abs_mul, abs_of_nonneg (hμ m hm)]
  exact (mul_le_mul_of_nonneg_left (realJacobi_abs_le n m) (hμ m hm)).trans_eq (mul_one _)

theorem weighted_jacobi_moment_expansion {ι : Type*} [Fintype ι]
    (T : Finset ℕ) (μ : ℕ → ℝ) (s : ι → ℕ) (a : ι → ℝ) (q : ℕ) :
    (∑ m ∈ T, μ m * (∑ i, a i * realJacobi (s i) m) ^ q) =
      ∑ t : Fin q → ι, (∏ j, a (t j)) *
        ∑ m ∈ T, μ m * realJacobi (∏ j, s (t j)) m := by
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib, ← realJacobi_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Bonami controls the square products. Every remaining product pays only
the supplied finite nonsquare-character error `E`. -/
theorem weighted_jacobi_even_moment_bound (hB : PublishedBonamiBound)
    (P S T : Finset ℕ) (hS : ∀ s ∈ S, Squarefree s)
    (hP : ∀ s ∈ S, s.primeFactors ⊆ P) (μ : ℕ → ℝ)
    (hμ : ∀ m ∈ T, 0 ≤ μ m) (a : S → ℝ) (l : ℕ) (hl : 0 < l)
    (E : ℝ) (hE : 0 ≤ E)
    (hns : ∀ t : Fin (2 * l) → S, ¬IsSquare (∏ j, (t j).val) →
      |∑ m ∈ T, μ m * realJacobi (∏ j, (t j).val) m| ≤ E) :
    (∑ m ∈ T, μ m * |∑ s : S, a s * realJacobi s.val m| ^ (2 * l)) ≤
      (∑ m ∈ T, μ m) *
        (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * |a s| ^ 2) ^ l +
      E * (∑ s : S, |a s|) ^ (2 * l) := by
  classical
  let W := ∑ m ∈ T, μ m
  have hW : 0 ≤ W := Finset.sum_nonneg hμ
  have hJ (t : Fin (2 * l) → S) :
      |∑ m ∈ T, μ m * realJacobi (∏ j, (t j).val) m| ≤
        W * (if IsSquare (∏ j, (t j).val) then 1 else 0) + E := by
    split_ifs with ht
    · have hh := weighted_jacobi_abs_le_mass T μ hμ (∏ j, (t j).val)
      dsimp [W]
      linarith
    · simpa only [mul_zero, zero_add] using hns t ht
  simp only [Even.pow_abs (even_two_mul l)]
  rw [weighted_jacobi_moment_expansion]
  calc
    _ ≤ ∑ t : Fin (2 * l) → S, (∏ j, |a (t j)|) *
        (W * (if IsSquare (∏ j, (t j).val) then 1 else 0) + E) := by
      apply Finset.sum_le_sum
      intro t ht
      calc
        _ ≤ |(∏ j, a (t j)) * ∑ m ∈ T, μ m * realJacobi (∏ j, (t j).val) m| := le_abs_self _
        _ = (∏ j, |a (t j)|) * |∑ m ∈ T, μ m * realJacobi (∏ j, (t j).val) m| := by
          rw [abs_mul, Finset.abs_prod]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hJ t) (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    _ = W * (∑ t : Fin (2 * l) → S, (∏ j, |a (t j)|) *
        (if IsSquare (∏ j, (t j).val) then 1 else 0)) + E * (∑ s : S, |a s|) ^ (2 * l) := by
      rw [Fintype.sum_pow, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left
      (squarefree_diagonal_bonami hB P S hS hP (fun s => |a s|) l hl) hW) _

end Ostmann

end OAI
