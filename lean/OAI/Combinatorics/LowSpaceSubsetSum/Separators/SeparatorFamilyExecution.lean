import OAI.Combinatorics.LowSpaceSubsetSum.Storage.FixedSizeFamilyExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.PreparedSeparatorExpectation

namespace OAI

/-! # Constructing all four separator families from their bounded draws

The outer recursion has exactly four stages in the application. The returned
row function contains stored arrays, and lookup traverses at most four tags.
-/

noncomputable section

namespace LowSpaceSubsetSum.SeparatorFamilyExecution

open scoped BigOperators

def coupling (n g r : ℕ) (k m : Fin r → ℕ) (hk : ∀ i, k i ≤ g) :=
  SamplerCoupling.pi r (fun i => Fin (m i) → SeparatorSample
    (Finset.univ : Finset (Fin g)) (k i))
    (fun i => FixedSizeFamilyExecution.coupling n g (k i) (hk i) (m i))

def execution (n g r : ℕ) (k m : Fin r → ℕ) (hk : ∀ i, k i ≤ g) :
    SamplerExecution.Execution (coupling n g r k m hk) :=
  SamplerExecution.pi r _ _ (fun i =>
    FixedSizeFamilyExecution.execution n g (k i) (hk i) (m i))

def run (n g : ℕ) : (r : ℕ) → (k m : Fin r → ℕ) → (hk : ∀ i, k i ≤ g) →
    (coupling n g r k m hk).Seed → Option (Fin r → Array (Fin (2 ^ g))) × ℕ
  | 0, _, _, _, _ => (some Fin.elim0, 1)
  | r + 1, k, m, hk, s =>
    let first := FixedSizeFamilyExecution.materialize n g (k 0) (hk 0) (m 0) s.1
    match first.1 with
    | none => (none, first.2 + 1)
    | some row =>
      let rest := run n g r (fun i => k i.succ) (fun i => m i.succ)
        (fun i => hk i.succ) s.2
      (rest.1.map (Fin.cons row), first.2 + rest.2 + 3)

theorem value (n g r : ℕ) (k m : Fin r → ℕ) (hk : ∀ i, k i ≤ g)
    (s : (coupling n g r k m hk).Seed) :
    (run n g r k m hk s).1 = ((execution n g r k m hk).run s).value.map
      (fun draws i => Array.ofFn (fun j => SeparatorStoredMasks.code (draws i j).val)) := by
  induction r with
  | zero =>
    simp only [run, execution, SamplerExecution.pi, SamplerExecution.pure, Option.map_some]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ r ih =>
    rcases s with ⟨head, tail⟩
    have hi := ih (fun i => k i.succ) (fun i => m i.succ) (fun i => hk i.succ) tail
    have hrow := FixedSizeFamilyExecution.materialize_value n g (k 0) (hk 0) (m 0) head
    cases hf : ((FixedSizeFamilyExecution.execution n g (k 0) (hk 0) (m 0)).run head).value with
    | none =>
      rw [hf] at hrow
      simp only [Option.map_none] at hrow
      simp only [run, hrow]
      simp only [execution, SamplerExecution.pi, SamplerExecution.map,
        SamplerExecution.prod, SamplerExecution.bind, hf, ↓reduceIte, Option.map_none]
    | some a =>
      have ha := (FixedSizeFamilyExecution.execution n g (k 0) (hk 0) (m 0)).ideal_eq_of_some
        head a hf
      rw [hf] at hrow
      simp only [Option.map_some] at hrow
      simp only [run, hrow]
      simp only [execution, SamplerExecution.pi, SamplerExecution.map,
        SamplerExecution.prod, SamplerExecution.bind, hf, reduceCtorEq, ↓reduceIte,
        Option.map_map]
      rw [hi]
      simp only [Option.map_map]
      congr 1
      funext draws i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Function.comp_apply, Fin.cons_zero, ha]
        rfl
      · simp only [Function.comp_apply, Fin.cons_succ]
        rfl

theorem work (n g r : ℕ) (k m : Fin r → ℕ) (hk : ∀ i, k i ≤ g)
    (s : (coupling n g r k m hk).Seed) :
    (run n g r k m hk s).2 ≤
      (∑ i, (m i * (g * n ^ 3 + 32 * (g + 1) ^ 3 + 4) + 5)) + 1 := by
  induction r with
  | zero => simp only [run, Fin.sum_univ_zero, Nat.zero_add, le_refl]
  | succ r ih =>
    have hf := FixedSizeFamilyExecution.materialize_work n g (k 0) (hk 0) (m 0) s.1
    have hr := ih (fun i => k i.succ) (fun i => m i.succ) (fun i => hk i.succ) s.2
    simp only [run, Fin.sum_univ_succ]
    split
    · dsimp only; omega
    · dsimp only; omega

namespace Application

variable {g : ℕ} (S : SeparatorExpectation.RoundedParameters g)

def run (n : ℕ) (s : (S.samplerCoupling n).Seed) :=
  SeparatorFamilyExecution.run n g 4 S.e S.counts S.size_le s

theorem value (n : ℕ) (s : (S.samplerCoupling n).Seed) :
    (run S n s).1 = ((S.samplerExecution n).run s).value.map
      (PreparedSeparatorExpectation.codes S) := by
  have h := SeparatorFamilyExecution.value n g 4 S.e S.counts S.size_le s
  apply h.trans
  change Option.map _ ((S.samplerExecution n).run s).value = _
  congr 1
  funext draws i
  simp only [PreparedSeparatorExpectation.codes, SeparatorExpectation.familyArrays,
    Array.map_ofFn]
  rfl

theorem sizes (n : ℕ) (s : (S.samplerCoupling n).Seed)
    (A : Fin 4 → Array (Fin (2 ^ g))) (h : (run S n s).1 = some A) (i : Fin 4) :
    (A i).size ≤ 11 * 2 ^ g := by
  rw [value] at h
  obtain ⟨draws, _, rfl⟩ := Option.map_eq_some_iff.mp h
  exact PreparedSeparatorExpectation.codes_size S draws i

theorem work (n : ℕ) (s : (S.samplerCoupling n).Seed) :
    (run S n s).2 ≤ 44 * 2 ^ g * (g * n ^ 3 + 32 * (g + 1) ^ 3 + 4) + 21 := by
  have h := SeparatorFamilyExecution.work n g 4 S.e S.counts S.size_le s
  have hm := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    Nat.add_le_add_right (Nat.mul_le_mul_right
      (g * n ^ 3 + 32 * (g + 1) ^ 3 + 4) (S.counts_le i)) 5)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hm
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hm h
  change (SeparatorFamilyExecution.run n g 4 S.e S.counts S.size_le s).2 ≤ _
  nlinarith only [h, hm]

end Application
end LowSpaceSubsetSum.SeparatorFamilyExecution

end

end OAI
