import OAI.Combinatorics.LowSpaceSubsetSum.Storage.FixedSizeSampleCells
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorFamilyExecution

namespace OAI

/-! # Live storage of all bounded separator-family draws

The trace counts accepted packed codes, their list-to-array conversion,
and the unused tails of supplied finite seed tuples on failure. The outer
application has four rows; no rejection sampler runs without its bound.
-/

noncomputable section
namespace LowSpaceSubsetSum.SeparatorSamplerCells

open scoped BigOperators

def family (n g k : ℕ) (hk : k ≤ g) : (m : ℕ) →
    (FixedSizeFamilyExecution.coupling n g k hk m).Seed →
      (Option (List (Fin (2^g))) × ℕ) × ℕ
  | 0, _ => ((some [], 1), 16)
  | m+1, s =>
    let first := FixedSizeSampleCells.run n g k s.1
    match first.1.1 with
    | none => ((none, first.1.2+1),
        first.2+m*(FixedSizeSampleCells.reserve n g+16)+16)
    | some code =>
      let tail := family n g k hk m s.2
      ((tail.1.1.map (code :: ·), first.1.2+tail.1.2+3), first.2+tail.2+16)

theorem family_value (n g k : ℕ) (hk : k ≤ g) (m : ℕ)
    (s : (FixedSizeFamilyExecution.coupling n g k hk m).Seed) :
    (family n g k hk m s).1 = FixedSizeFamilyExecution.run n g k hk m s := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hh := FixedSizeSampleCells.run_value n g k s.1
    have ht := ih s.2
    have hh₁ := congrArg Prod.fst hh
    have hh₂ := congrArg Prod.snd hh
    have ht₁ := congrArg Prod.fst ht
    have ht₂ := congrArg Prod.snd ht
    simp only [family, FixedSizeFamilyExecution.run, hh₁, hh₂, ht₁, ht₂]
    split <;> simp_all only

theorem family_cells (n g k : ℕ) (hk : k ≤ g) (m : ℕ)
    (s : (FixedSizeFamilyExecution.coupling n g k hk m).Seed) :
    (family n g k hk m s).2 ≤ m*(FixedSizeSampleCells.reserve n g+16)+16 := by
  induction m with
  | zero => simp only [family, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ m ih =>
    have hf := FixedSizeSampleCells.run_cells n g k s.1
    have ht := ih s.2
    simp only [family]
    split <;> dsimp only <;> nlinarith only [hf, ht]

def materialize (n g k : ℕ) (hk : k ≤ g) (m : ℕ)
    (s : (FixedSizeFamilyExecution.coupling n g k hk m).Seed) :
    (Option (Array (Fin (2^g))) × ℕ) × ℕ :=
  let r := family n g k hk m s
  ((r.1.1.map List.toArray, r.1.2+m+1), r.2+2*m+16)

theorem materialize_value (n g k : ℕ) (hk : k ≤ g) (m : ℕ)
    (s : (FixedSizeFamilyExecution.coupling n g k hk m).Seed) :
    (materialize n g k hk m s).1 = FixedSizeFamilyExecution.materialize n g k hk m s := by
  have h := family_value n g k hk m s
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [materialize, FixedSizeFamilyExecution.materialize, h₁, h₂]

theorem materialize_cells (n g k : ℕ) (hk : k ≤ g) (m : ℕ)
    (s : (FixedSizeFamilyExecution.coupling n g k hk m).Seed) :
    (materialize n g k hk m s).2 ≤ m*(FixedSizeSampleCells.reserve n g+18)+32 := by
  have h := family_cells n g k hk m s
  change _+2*m+16 ≤ _
  nlinarith only [h]

def rowReserve (n g m : ℕ) : ℕ := m*(FixedSizeSampleCells.reserve n g+18)+48

def run (n g : ℕ) : (r : ℕ) → (k m : Fin r → ℕ) → (hk : ∀ i, k i ≤ g) →
    (SeparatorFamilyExecution.coupling n g r k m hk).Seed →
      (Option (Fin r → Array (Fin (2^g))) × ℕ) × ℕ
  | 0, _, _, _, _ => ((some Fin.elim0, 1), 16)
  | r+1, k, m, hk, s =>
    let first := materialize n g (k 0) (hk 0) (m 0) s.1
    match first.1.1 with
    | none => ((none, first.1.2+1),
        first.2+(∑ i : Fin r, rowReserve n g (m i.succ))+16)
    | some row =>
      let tail := run n g r (fun i => k i.succ) (fun i => m i.succ)
        (fun i => hk i.succ) s.2
      ((tail.1.1.map (Fin.cons row), first.1.2+tail.1.2+3), first.2+tail.2+16)

theorem run_value (n g r : ℕ) (k m : Fin r → ℕ) (hk : ∀ i, k i ≤ g)
    (s : (SeparatorFamilyExecution.coupling n g r k m hk).Seed) :
    (run n g r k m hk s).1 = SeparatorFamilyExecution.run n g r k m hk s := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hh := materialize_value n g (k 0) (hk 0) (m 0) s.1
    have ht := ih (fun i => k i.succ) (fun i => m i.succ) (fun i => hk i.succ) s.2
    have hh₁ := congrArg Prod.fst hh
    have hh₂ := congrArg Prod.snd hh
    have ht₁ := congrArg Prod.fst ht
    have ht₂ := congrArg Prod.snd ht
    simp only [run, SeparatorFamilyExecution.run, hh₁, hh₂, ht₁, ht₂]
    split <;> simp_all only

theorem run_cells (n g r : ℕ) (k m : Fin r → ℕ) (hk : ∀ i, k i ≤ g)
    (s : (SeparatorFamilyExecution.coupling n g r k m hk).Seed) :
    (run n g r k m hk s).2 ≤ (∑ i, rowReserve n g (m i))+16 := by
  induction r with
  | zero => simp only [run, Fin.sum_univ_zero, Nat.zero_add, le_refl]
  | succ r ih =>
    have hf := materialize_cells n g (k 0) (hk 0) (m 0) s.1
    have ht := ih (fun i => k i.succ) (fun i => m i.succ) (fun i => hk i.succ) s.2
    simp only [run, Fin.sum_univ_succ]
    split <;> dsimp only <;> unfold rowReserve at * <;> omega

theorem four_cells (n g : ℕ) (k m : Fin 4 → ℕ) (hk : ∀ i, k i ≤ g)
    (hm : ∀ i, m i ≤ 11*2^g)
    (s : (SeparatorFamilyExecution.coupling n g 4 k m hk).Seed) :
    (run n g 4 k m hk s).2 ≤
      4*(11*2^g*(FixedSizeSampleCells.reserve n g+18)+48)+16 := by
  have h := run_cells n g 4 k m hk s
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    Nat.add_le_add_right (Nat.mul_le_mul_right (FixedSizeSampleCells.reserve n g+18) (hm i)) 48)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact h.trans (Nat.add_le_add_right hsum 16)

end LowSpaceSubsetSum.SeparatorSamplerCells

end

end OAI
