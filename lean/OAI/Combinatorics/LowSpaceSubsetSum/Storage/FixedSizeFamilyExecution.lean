import OAI.Combinatorics.LowSpaceSubsetSum.Storage.FixedSizeCodeExecution

namespace OAI

/-! # Sequential construction of a sampled separator family

Every occurrence uses its own bounded fixed-size draw. Exhaustion stops the
remaining draws; successful occurrences retain their order and multiplicity.
-/

noncomputable section

namespace LowSpaceSubsetSum.FixedSizeFamilyExecution

def coupling (n g k : ℕ) (hk : k ≤ g) (m : ℕ) :=
  SamplerCoupling.pi m (fun _ => SeparatorSample (Finset.univ : Finset (Fin g)) k)
    (fun _ => fixedSizeCoupling n g k hk)

def execution (n g k : ℕ) (hk : k ≤ g) (m : ℕ) :
    SamplerExecution.Execution (coupling n g k hk m) :=
  SamplerExecution.pi m _ _ (fun _ => SamplerExecution.fixedSize n g k hk)

def run (n g k : ℕ) (hk : k ≤ g) : (m : ℕ) →
    (coupling n g k hk m).Seed → Option (List (Fin (2 ^ g))) × ℕ
  | 0, _ => (some [], 1)
  | m + 1, s =>
    let first := FixedSizeCodeExecution.run n g k s.1
    match first.1 with
    | none => (none, first.2 + 1)
    | some code =>
      let rest := run n g k hk m s.2
      (rest.1.map (code :: ·), first.2 + rest.2 + 3)

theorem value (n g k : ℕ) (hk : k ≤ g) (m : ℕ) (s : (coupling n g k hk m).Seed) :
    (run n g k hk m s).1 = ((execution n g k hk m).run s).value.map
      (fun draws => List.ofFn (fun i => SeparatorStoredMasks.code (draws i).val)) := by
  induction m with
  | zero => simp [run, execution, SamplerExecution.pi, SamplerExecution.pure]
  | succ m ih =>
    rcases s with ⟨head, tail⟩
    have hi := ih tail
    have hcode := FixedSizeCodeExecution.value n g k hk head
    cases hf : ((SamplerExecution.fixedSize n g k hk).run head).value with
    | none =>
      rw [hf] at hcode
      simp only [Option.map_none] at hcode
      simp only [run, hcode]
      simp only [execution, SamplerExecution.pi, SamplerExecution.map,
        SamplerExecution.prod, SamplerExecution.bind, hf, ↓reduceIte, Option.map_none]
    | some a =>
      have ha := (SamplerExecution.fixedSize n g k hk).ideal_eq_of_some head a hf
      rw [hf] at hcode
      simp only [Option.map_some] at hcode
      simp only [run, hcode]
      simp only [execution, SamplerExecution.pi, SamplerExecution.map,
        SamplerExecution.prod, SamplerExecution.bind, hf, reduceCtorEq, ↓reduceIte,
        Option.map_map]
      rw [hi]
      simp only [Option.map_map]
      congr 1
      funext draws
      simp only [Function.comp_apply, List.ofFn_succ, ha]
      rfl

theorem work (n g k : ℕ) (hk : k ≤ g) (m : ℕ) (s : (coupling n g k hk m).Seed) :
    (run n g k hk m s).2 ≤ m * (g * n ^ 3 + 32 * (g + 1) ^ 3 + 3) + 1 := by
  induction m with
  | zero => simp only [run, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ m ih =>
    have hf := FixedSizeCodeExecution.work n g k s.1
    have hr := ih s.2
    simp only [run]
    split
    · dsimp only; nlinarith only [hf, Nat.zero_le (m * (g * n ^ 3 + 32 * (g + 1) ^ 3 + 3))]
    · dsimp only; nlinarith only [hf, hr]

def materialize (n g k : ℕ) (hk : k ≤ g) (m : ℕ)
    (s : (coupling n g k hk m).Seed) : Option (Array (Fin (2 ^ g))) × ℕ :=
  let out := run n g k hk m s
  (out.1.map List.toArray, out.2 + m + 1)

theorem materialize_value (n g k : ℕ) (hk : k ≤ g) (m : ℕ)
    (s : (coupling n g k hk m).Seed) :
    (materialize n g k hk m s).1 = ((execution n g k hk m).run s).value.map
      (fun draws => Array.ofFn (fun i => SeparatorStoredMasks.code (draws i).val)) := by
  simp only [materialize, value, Option.map_map]
  congr 1
  funext draws
  simp only [Function.comp_apply, List.toArray_ofFn]

theorem materialize_work (n g k : ℕ) (hk : k ≤ g) (m : ℕ)
    (s : (coupling n g k hk m).Seed) :
    (materialize n g k hk m s).2 ≤ m * (g * n ^ 3 + 32 * (g + 1) ^ 3 + 4) + 2 := by
  have h := work n g k hk m s
  change _ + m + 1 ≤ _
  nlinarith only [h]

theorem materialize_size (n g k : ℕ) (hk : k ≤ g) (m : ℕ)
    (s : (coupling n g k hk m).Seed) (A : Array (Fin (2 ^ g)))
    (h : (materialize n g k hk m s).1 = some A) : A.size = m := by
  rw [materialize_value] at h
  obtain ⟨draws, _, rfl⟩ := Option.map_eq_some_iff.mp h
  exact Array.size_ofFn

end LowSpaceSubsetSum.FixedSizeFamilyExecution

end

end OAI
