import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationSamplerCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PartitionArrayExecution

namespace OAI

/-! # Live candidate, permutation, and balanced-label arrays

Only the accepted label vector survives a component. During construction
the digits, temporary permutation, and label vector are all counted. The
sequential family retains earlier label vectors while later draws run.
-/

noncomputable section
namespace LowSpaceSubsetSum.PartitionLabelCells

variable {n : ℕ}

def run (n : ℕ) (j : Fin 3) (s : (permutationCoupling n (PartitionLabelExecution.size n j)).Seed) :
    (Option (PartitionArrayExecution.Labels n j) × ℕ) × ℕ :=
  let digits := PermutationSamplerCells.run n (PartitionLabelExecution.size n j) s
  match digits.1.value with
  | none => ((none, digits.1.reads+digits.1.tests+1), digits.2+16)
  | some d =>
    let p := PermutationArray.build (PartitionLabelExecution.size n j) d
    let labels : PartitionArrayExecution.Labels n j :=
      p.1.map (fun k => (finProdFinEquiv.symm k).1)
    ((some labels, digits.1.reads+digits.1.tests+p.2+4*PartitionLabelExecution.size n j+3),
      digits.2+PermutationArray.peakCells (PartitionLabelExecution.size n j)+
        3*PartitionLabelExecution.size n j+24)

theorem run_value (n : ℕ) (j : Fin 3)
    (s : (permutationCoupling n (PartitionLabelExecution.size n j)).Seed) :
    (run n j s).1 = PartitionLabelExecution.run n j s := by
  simp only [run, PermutationSamplerCells.run_value, PartitionLabelExecution.run]
  split <;> simp_all only

theorem run_cells (n : ℕ) (j : Fin 3)
    (s : (permutationCoupling n (PartitionLabelExecution.size n j)).Seed) :
    (run n j s).2 ≤ (PartitionLabelExecution.size n j+1)*(3*n^3+128) := by
  have hd := PermutationSamplerCells.run_cells n (PartitionLabelExecution.size n j) s
  have hp := PermutationArray.peakCells_bound (PartitionLabelExecution.size n j)
  simp only [run]
  split <;> dsimp only <;> nlinarith only [hd, hp, Nat.zero_le (n^3)]

theorem size_eq (n : ℕ) (j : Fin 3) : PartitionLabelExecution.size n j = mixerSize n := by
  fin_cases j <;> simp [PartitionLabelExecution.size, RepresentationSetup.blockCount,
    RepresentationSetup.blockHalf, mixerSize] <;> omega

def family (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) :
    (k : ℕ) → (j : Fin k → Fin 3) → (PartitionArrayExecution.coupling R z k j).Seed →
      (Option (∀ i, PartitionArrayExecution.Labels n (j i)) × ℕ) × ℕ
  | 0, _, _ => ((some (fun i => Fin.elim0 i), 1), 16)
  | k+1, j, s =>
    let head := run n (j 0) s.1
    match head.1.1 with
    | none => ((none, head.1.2+1),
        head.2+k*((mixerSize n+1)*(3*n^3+160))+8)
    | some labels =>
      let tail := family R z k (fun i => j i.succ) s.2
      ((tail.1.1.map (Fin.cons labels), head.1.2+tail.1.2+3),
        head.2+tail.2+2*PartitionLabelExecution.size n (j 0)+12)

theorem family_value (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (k : ℕ) (j : Fin k → Fin 3) (s : (PartitionArrayExecution.coupling R z k j).Seed) :
    (family R z k j s).1 = PartitionArrayExecution.run R z k j s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hh := run_value n (j 0) s.1
    have ht := ih (fun i => j i.succ) s.2
    have hh₁ := congrArg Prod.fst hh
    have hh₂ := congrArg Prod.snd hh
    have ht₁ := congrArg Prod.fst ht
    have ht₂ := congrArg Prod.snd ht
    simp only [family, PartitionArrayExecution.run, hh₁, hh₂, ht₁, ht₂]
    split <;> simp_all only

theorem family_cells (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (k : ℕ) (j : Fin k → Fin 3) (s : (PartitionArrayExecution.coupling R z k j).Seed) :
    (family R z k j s).2 ≤ k*((mixerSize n+1)*(3*n^3+160))+16 := by
  induction k with
  | zero => simp only [family, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ k ih =>
    have hh := run_cells n (j 0) s.1
    rw [size_eq] at hh
    have ht := ih (fun i => j i.succ) s.2
    simp only [family]
    split
    · dsimp only
      nlinarith only [hh, Nat.zero_le (k*((mixerSize n+1)*(3*n^3+160)))]
    · dsimp only
      rw [size_eq]
      nlinarith only [hh, ht, Nat.zero_le (mixerSize n)]

end LowSpaceSubsetSum.PartitionLabelCells

end

end OAI
