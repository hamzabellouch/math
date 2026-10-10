import OAI.Analysis.MutuallyUnbiased.Matrix.Hadamard
import OAI.Analysis.MutuallyUnbiased.Cubic.CubicSupportBridge
import OAI.Analysis.MutuallyUnbiased.Cubic.CubicPattern

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem hadamard_row_ratio_moments {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) (r s : Coord) (hrs : r ≠ s) :
    (∀ j, Complex.normSq (H r j / H s j) = 1) ∧
      (∑ j, H r j / H s j) = 0 ∧ (∑ j, (H r j / H s j) ^ 2) = 0 := by
  refine ⟨fun j => ?_, ?_, ?_⟩
  · simp [hH.1]
  · simp_rw [div_eq_mul_inv, unit_inv_eq_conj (hH.1 s _)]
    simpa [hrs] using hH.row_orthogonal r s
  · have he (j : Coord) : (H r j / H s j) ^ 2 =
        H r j ^ 2 * conj (H s j ^ 2) := by
      rw [div_pow, div_eq_mul_inv, unit_inv_eq_conj (hH2.1 s j)]
    simp_rw [he]
    simpa [hrs] using hH2.row_orthogonal r s

theorem cubed_row_ratio_pattern {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) (r s : Coord) (hrs : r ≠ s) :
    TwoValuePattern (fun j => H r j ^ 3 / H s j ^ 3) := by
  obtain ⟨hu, h1, h2⟩ := hadamard_row_ratio_moments hH hH2 r s hrs
  simpa only [div_pow] using cubed_entries_twoValuePattern
    (fun j => H r j / H s j) hu h1 h2

theorem twoValuePattern_constant (a : ℂ) : TwoValuePattern (fun _ : Coord => a) := by
  refine ⟨⟨a, a, fun _ => Or.inl rfl⟩, ?_⟩
  intro b ⟨i, hi⟩ ⟨j, hj⟩
  exact False.elim (hj hi)

theorem cubed_row_pattern {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) (h0 : ∀ j, H 0 j = 1)
    (r : Coord) : TwoValuePattern (fun j => H r j ^ 3) := by
  by_cases hr : r = 0
  · subst r
    simpa only [h0, one_pow] using twoValuePattern_constant 1
  · simpa only [h0, one_pow, div_one] using cubed_row_ratio_pattern hH hH2 r 0 hr

/-- Before excluding it with the three-by-three block obstruction, the only
possible failure of cube roots after dephasing has one constant block. -/
theorem dephased_hadamard_cubes_block {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2))
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1)
    (i j : Coord) (hij : H i j ^ 3 ≠ 1) :
    ∃ (R S : Finset Coord) (x : ℂ),
      R.card = 3 ∧ S.card = 3 ∧ (0 : Coord) ∉ R ∧ (0 : Coord) ∉ S ∧
      x ≠ 0 ∧ x ≠ 1 ∧
      ∀ r c, H r c ^ 3 = if r ∈ R ∧ c ∈ S then x else 1 := by
  apply dephased_pattern_single_block (fun r c => H r c ^ 3)
    (fun j => by rw [h0row, one_pow]) (fun i => by rw [h0col, one_pow])
    (fun r c => pow_ne_zero _ (unit_ne_zero (hH.1 r c)))
    (cubed_row_pattern hH hH2 h0row) ?_
    (cubed_row_ratio_pattern hH hH2) i j hij
  intro c
  exact cubed_row_pattern hH.transpose hH2.transpose h0col c

end MUB6

end

end OAI
