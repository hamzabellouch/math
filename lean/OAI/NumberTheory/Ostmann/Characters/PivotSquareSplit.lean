import OAI.NumberTheory.Ostmann.Characters.PivotSquareExpansion
import OAI.NumberTheory.Ostmann.Construction.TransferFrequencyRange

namespace OAI

/-! # Exact diagonal and signed-frequency decomposition of a transfer -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- A finite family has a nonnegative equal-key square even when its keys
range over an infinite type. -/
theorem finite_key_square_nonneg {A K : Type*} [Fintype A]
    (key : A → K) (c : A → ℂ) :
    0 ≤ (∑ a, ∑ b, if key a = key b then c a * conj (c b) else 0).re := by
  classical
  let T : Finset K := Finset.univ.image key
  let k : A → T := fun a => ⟨key a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  have h := diagonal_real_nonneg k c (fun _ => 1) (fun _ => by norm_num)
  simpa only [Complex.ofReal_one, one_mul, k, Subtype.mk.injEq, Complex.star_def] using h

noncomputable def pivotDiagonal {A : Type*} [Fintype A]
    (L : A → ℕ) (v : A → ℤ) (c : A → ℂ) : ℂ :=
  ∑ a, ∑ b, if v a * L b - v b * L a = 0 then c a * conj (c b) else 0

noncomputable def pivotOffDiagonal {A : Type*} [Fintype A]
    (M : ℕ) (L : A → ℕ) (v : A → ℤ) (c : A → ℂ) : ℂ :=
  ∑ a, ∑ b, if v a * L b - v b * L a ≠ 0 ∧ (M : ℤ) ∣ v a * L b - v b * L a
    then c a * conj (c b) else 0

theorem pivot_square_split {A : Type*} [Fintype A]
    (M : ℕ) [NeZero M] (L : A → ℕ) (v : A → ℤ)
    (hL : ∀ a, (L a).Coprime M) (c : A → ℂ) :
    (∑ u : Fin M, ‖groupedCoefficient (fun a => pivotResidueKey M (L a) (v a)) c u‖ ^ 2) =
      (pivotDiagonal L v c).re + (pivotOffDiagonal M L v c).re := by
  rw [pivot_square_expansion M L v hL c, ← Complex.add_re]
  congr 1
  unfold pivotDiagonal pivotOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hzero : v a * L b - v b * L a = 0
  · simp only [hzero, ne_eq, not_true_eq_false, false_and, ite_false, add_zero,
      dvd_zero, ite_true]
  · by_cases hd : (M : ℤ) ∣ v a * L b - v b * L a <;> simp [hzero, hd]

theorem pivotDiagonal_nonneg {A : Type*} [Fintype A]
    (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hLpos : ∀ a, 0 < L a) (hv : ∀ a, v a ≠ 0)
    (hlarge : ∀ a q, q.Prime → q ∣ L a → (v a).natAbs < q) :
    0 ≤ (pivotDiagonal L v c).re := by
  rw [pivotDiagonal, pivot_diagonal_expansion L v c hLpos hv hlarge]
  convert finite_key_square_nonneg (fun a => (L a, v a)) c using 1
  congr 2
  funext a
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : (L a, v a) = (L b, v b) <;> simp only [h, ite_true, ite_false]

/-- The off-diagonal is indexed by the genuine signed output frequency,
with no extra multiplicity. -/
theorem pivotOffDiagonal_eq_frequency_sum {A : Type*} [Fintype A]
    (M B H V : ℕ) (hM : 0 < M) (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hv : ∀ a, (v a).natAbs ≤ B) (hL : ∀ a, L a ≤ H)
    (hscale : 2 * B * H ≤ V * M) :
    pivotOffDiagonal M L v c = ∑ s ∈ transferFrequencyRange V,
      ∑ a, ∑ b, if s ≠ 0 ∧ v a * L b - v b * L a = s * M
        then c a * conj (c b) else 0 := by
  unfold pivotOffDiagonal
  simp_rw [transferred_frequency_sum_bounded M _ _ B H V hM _ _
    (hv _) (hv _) (hL _) (hL _) hscale]
  calc
    _ = ∑ a, ∑ s ∈ transferFrequencyRange V, ∑ b,
        if s ≠ 0 ∧ v a * L b - v b * L a = s * M then c a * conj (c b) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

end Ostmann

end OAI
