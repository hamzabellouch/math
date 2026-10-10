import OAI.Analysis.MutuallyUnbiased.Cubic.CubicRoots
import OAI.Analysis.MutuallyUnbiased.Cubic.CubicHadamard

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem cubic_hadamard_row_sum {H : CMatrix} (hH : IsHadamard H)
    (h0row : ∀ j, H 0 j = 1) (r : Coord) (hr : r ≠ 0) : ∑ j, H r j = 0 := by
  simpa [h0row, hr] using hH.row_orthogonal r 0

theorem cubic_hadamard_row_one_count {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1)
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1) (r : Fin 5) :
    (Finset.univ.filter (fun j : Fin 5 => H r.succ j.succ = 1)).card = 1 := by
  classical
  have hc := cube_roots_one_count (fun j => H r.succ j) (hcube r.succ)
    (cubic_hadamard_row_sum hH h0row r.succ (Fin.succ_ne_zero _))
  rw [Fin.card_filter_univ_succ] at hc
  simp only [h0col, ite_true] at hc
  omega

theorem existsUnique_of_filter_card_one (p : Fin 5 → Prop) [DecidablePred p]
    (hc : (Finset.univ.filter p).card = 1) : ∃! i, p i := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  have hmem : ∀ j, p j ↔ j = i := by
    intro j
    have hh := congrArg (fun S : Finset (Fin 5) => j ∈ S) hi
    simpa using hh
  exact ⟨i, (hmem i).mpr rfl, fun j hj => (hmem j).mp hj⟩

/-- The noninitial entries equal to one form a perfect matching. -/
theorem cubic_hadamard_one_matching {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1)
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1) :
    ∃ p : Equiv.Perm (Fin 5), ∀ i j, H i.succ (p j).succ = 1 ↔ i = j := by
  classical
  have hrow : ∀ i : Fin 5, ∃! j : Fin 5, H i.succ j.succ = 1 := fun i =>
    existsUnique_of_filter_card_one _ (cubic_hadamard_row_one_count hH hcube h0row h0col i)
  have hcol : ∀ j : Fin 5, ∃! i : Fin 5, H i.succ j.succ = 1 := fun j =>
    existsUnique_of_filter_card_one _
      (cubic_hadamard_row_one_count hH.transpose (fun i j => hcube j i) h0col h0row j)
  choose f hf huniq using hrow
  have hinj : Function.Injective f := by
    intro i j hij
    exact (hcol (f i)).unique (hf i) (by rw [hij]; exact hf j)
  let p : Equiv.Perm (Fin 5) :=
    Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨p, fun i j => ?_⟩
  constructor
  · intro hij
    have h : f j = f i := huniq i (f j) hij
    exact (hinj h).symm
  · rintro rfl
    exact hf i

/-- Extend a permutation of the five noninitial coordinates by fixing zero. -/
def fixZeroPermutation (p : Equiv.Perm (Fin 5)) : Equiv.Perm Coord where
  toFun := Fin.cases 0 (fun i => (p i).succ)
  invFun := Fin.cases 0 (fun i => (p.symm i).succ)
  left_inv := by intro i; cases i using Fin.cases <;> simp
  right_inv := by intro i; cases i using Fin.cases <;> simp

@[simp] theorem fixZeroPermutation_zero (p : Equiv.Perm (Fin 5)) :
    fixZeroPermutation p 0 = 0 := rfl

@[simp] theorem fixZeroPermutation_succ (p : Equiv.Perm (Fin 5)) (i : Fin 5) :
    fixZeroPermutation p i.succ = (p i).succ := rfl

end MUB6

end

end OAI
