import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PartitionLabelExecution

namespace OAI

/-! # Sequential materialization of the three balanced partition arrays

The stored output consists only of labels in sorted mixer order. Every
component executes the bounded permutation sampler, and a failed component
stops the remaining draws. The source colorings appear only in refinement.
-/

noncomputable section
namespace LowSpaceSubsetSum.PartitionArrayExecution

variable {n : ℕ}

abbrev Labels (n : ℕ) (j : Fin 3) :=
  Vector (Fin (RepresentationSetup.blockCount j)) (PartitionLabelExecution.size n j)

def encode (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (j : Fin 3)
    (f : R.Partition z j) : Labels n j :=
  Vector.ofFn (fun k => f.val ((CanonicalPartition.ranks R z j).symm k))

theorem component_value (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (j : Fin 3) (s : (CanonicalPartition.coupling R z j).Seed) :
    (PartitionLabelExecution.run n j s).1 =
      ((CanonicalPartition.execution R z j).run s).value.map (encode R z j) := by
  rw [(CanonicalPartition.execution R z j).value_eq]
  cases hs : (CanonicalPartition.coupling R z j).bounded s with
  | none =>
    cases hr : (PartitionLabelExecution.run n j s).1 with
    | none => rfl
    | some v =>
      obtain ⟨f, hf, _⟩ := PartitionLabelExecution.source_value R z j s v hr
      rw [hs] at hf
      contradiction
  | some f =>
    obtain ⟨v, hv, he⟩ := PartitionLabelExecution.complete R z j s f hs
    rw [hv, Option.map_some]
    congr 1
    apply Vector.ext
    intro k hk
    exact (he ⟨k, hk⟩).trans (by simp [encode])

def coupling (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (k : ℕ) (j : Fin k → Fin 3) :=
  SamplerCoupling.pi k (fun i => R.Partition z (j i))
    (fun i => CanonicalPartition.coupling R z (j i))

def execution (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (k : ℕ) (j : Fin k → Fin 3) : SamplerExecution.Execution (coupling R z k j) :=
  SamplerExecution.pi k _ _ (fun i => CanonicalPartition.execution R z (j i))

def run (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) :
    (k : ℕ) → (j : Fin k → Fin 3) → (coupling R z k j).Seed →
      Option (∀ i, Labels n (j i)) × ℕ
  | 0, _, _ => (some (fun i => Fin.elim0 i), 1)
  | k + 1, j, s =>
    let head := PartitionLabelExecution.run n (j 0) s.1
    match head.1 with
    | none => (none, head.2 + 1)
    | some labels =>
      let tail := run R z k (fun i => j i.succ) s.2
      (tail.1.map (Fin.cons labels), head.2 + tail.2 + 3)

theorem value (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (k : ℕ) (j : Fin k → Fin 3) (s : (coupling R z k j).Seed) :
    (run R z k j s).1 = ((execution R z k j).run s).value.map
      (fun f i => encode R z (j i) (f i)) := by
  induction k with
  | zero =>
    simp only [run, execution, SamplerExecution.pi, SamplerExecution.pure, Option.map_some,
      Option.some.injEq]
    funext i
    exact Fin.elim0 i
  | succ k ih =>
    rcases s with ⟨head, tail⟩
    have hi := ih (fun i => j i.succ) tail
    have hc := component_value R z (j 0) head
    cases hf : ((CanonicalPartition.execution R z (j 0)).run head).value with
    | none =>
      rw [hf] at hc
      simp only [Option.map_none] at hc
      simp only [run, hc]
      simp only [execution, SamplerExecution.pi, SamplerExecution.map,
        SamplerExecution.prod, SamplerExecution.bind, hf, ↓reduceIte, Option.map_none]
    | some a =>
      have ha := (CanonicalPartition.execution R z (j 0)).ideal_eq_of_some head a hf
      rw [hf] at hc
      simp only [Option.map_some] at hc
      simp only [run, hc]
      simp only [execution, SamplerExecution.pi, SamplerExecution.map,
        SamplerExecution.prod, SamplerExecution.bind, hf, reduceCtorEq, ↓reduceIte,
        Option.map_map]
      rw [hi]
      simp only [Option.map_map]
      congr 1
      funext f
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.cons_zero, ha]
        rfl
      · simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.cons_succ]
        rfl

theorem component_work (n : ℕ) (j : Fin 3)
    (s : (permutationCoupling n (PartitionLabelExecution.size n j)).Seed) :
    (PartitionLabelExecution.run n j s).2 ≤
      mixerSize n * n ^ 3 + 10 * (mixerSize n + 1) ^ 2 + 4 * mixerSize n + 3 := by
  have he : PartitionLabelExecution.size n j = mixerSize n := by
    fin_cases j <;> simp [PartitionLabelExecution.size, RepresentationSetup.blockCount,
      RepresentationSetup.blockHalf, mixerSize] <;> omega
  simpa only [he] using PartitionLabelExecution.work n j s

theorem work (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (k : ℕ) (j : Fin k → Fin 3) (s : (coupling R z k j).Seed) :
    (run R z k j s).2 ≤
      k * (mixerSize n * n ^ 3 + 10 * (mixerSize n + 1) ^ 2 + 4 * mixerSize n + 6) + 1 := by
  induction k with
  | zero => simp only [run, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ k ih =>
    have hh := component_work n (j 0) s.1
    have ht := ih (fun i => j i.succ) s.2
    simp only [run]
    split
    · dsimp only; nlinarith only [hh, Nat.zero_le (k * (mixerSize n * n ^ 3 +
        10 * (mixerSize n + 1) ^ 2 + 4 * mixerSize n + 6))]
    · dsimp only; nlinarith only [hh, ht]

end LowSpaceSubsetSum.PartitionArrayExecution

end

end OAI
