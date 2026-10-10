import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CanonicalPartition
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationDigitsExecution

namespace OAI

/-! # Stored labels from an actual bounded mixer permutation

For each sorted mixer position, the accepted permutation rank determines its
consecutive block label by integer division. Only the resulting label array
is retained after the temporary permutation has been scanned.
-/

noncomputable section
namespace LowSpaceSubsetSum.PartitionLabelExecution

variable {n : ℕ}

abbrev size (n : ℕ) (j : Fin 3) : ℕ :=
  RepresentationSetup.blockCount j * (2 * RepresentationSetup.blockHalf n j)

def run (n : ℕ) (j : Fin 3) (s : (permutationCoupling n (size n j)).Seed) :
    Option (Vector (Fin (RepresentationSetup.blockCount j)) (size n j)) × ℕ :=
  let digits := PermutationDigitsExecution.run n (size n j) s
  match digits.value with
  | none => (none, digits.reads + digits.tests + 1)
  | some d =>
    let p := PermutationArray.build (size n j) d
    let labels : Vector (Fin (RepresentationSetup.blockCount j)) (size n j) := p.1.map (fun k => (finProdFinEquiv.symm k).1)
    (some labels, digits.reads + digits.tests + p.2 + 4 * size n j + 3)

theorem value (n : ℕ) (j : Fin 3) (s : (permutationCoupling n (size n j)).Seed)
    (v : Vector (Fin (RepresentationSetup.blockCount j)) (size n j))
    (h : (run n j s).1 = some v) :
    ∃ e : Equiv.Perm (Fin (size n j)), (permutationCoupling n (size n j)).bounded s = some e ∧
      ∀ k : Fin (size n j), v[k.val] = (finProdFinEquiv.symm (e k)).1 := by
  unfold run at h
  cases hd : (PermutationDigitsExecution.run n (size n j) s).value with
  | none => simp only [hd, reduceCtorEq] at h
  | some d =>
    simp only [hd, Option.some.injEq] at h
    subst v
    refine ⟨PermutationArray.semantic (size n j) d, ?_, ?_⟩
    · have hp := PermutationDigitsExecution.value n (size n j) s
      rw [hd] at hp
      rw [← (SamplerExecution.permutation n (size n j)).value_eq]
      exact hp.symm
    · intro k
      simp only [Vector.getElem_map, PermutationArray.build_value]

theorem label_source (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (j : Fin 3)
    (e : Equiv.Perm (Fin (size n j))) (k : Fin (size n j)) :
    (coloringOfPermutation (CanonicalPartition.base R z j)
      (Equiv.permCongr (CanonicalPartition.ranks R z j).symm e)).val
        ((CanonicalPartition.ranks R z j).symm k) = (finProdFinEquiv.symm (e k)).1 := by
  simp [coloringOfPermutation, CanonicalPartition.base, CanonicalPartition.labels,
    Equiv.permCongr_apply]

theorem source_value (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (j : Fin 3)
    (s : (CanonicalPartition.coupling R z j).Seed)
    (v : Vector (Fin (RepresentationSetup.blockCount j)) (size n j))
    (h : (run n j s).1 = some v) :
    ∃ f : R.Partition z j, (CanonicalPartition.coupling R z j).bounded s = some f ∧
      ∀ k : Fin (size n j), v[k.val] = f.val ((CanonicalPartition.ranks R z j).symm k) := by
  obtain ⟨e, he, hv⟩ := value n j s v h
  refine ⟨coloringOfPermutation (CanonicalPartition.base R z j)
    (Equiv.permCongr (CanonicalPartition.ranks R z j).symm e), ?_, ?_⟩
  · simp only [CanonicalPartition.coupling, SamplerCoupling.map, he, Option.map_some]
  · intro k
    exact (hv k).trans (label_source R z j e k).symm

theorem complete (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (j : Fin 3)
    (s : (CanonicalPartition.coupling R z j).Seed) (f : R.Partition z j)
    (h : (CanonicalPartition.coupling R z j).bounded s = some f) :
    ∃ v, (run n j s).1 = some v ∧
      ∀ k : Fin (size n j), v[k.val] = f.val ((CanonicalPartition.ranks R z j).symm k) := by
  cases hd : (PermutationDigitsExecution.run n (size n j) s).value with
  | none =>
    have hp := PermutationDigitsExecution.value n (size n j) s
    rw [hd] at hp
    have hp' : (permutationCoupling n (size n j)).bounded s = none := by
      exact ((SamplerExecution.permutation n (size n j)).value_eq s).symm.trans hp.symm
    simp only [CanonicalPartition.coupling, SamplerCoupling.map, hp', Option.map_none,
      reduceCtorEq] at h
  | some d =>
    let v : Vector (Fin (RepresentationSetup.blockCount j)) (size n j) :=
      (PermutationArray.build (size n j) d).1.map (fun k => (finProdFinEquiv.symm k).1)
    have hv : (run n j s).1 = some v := by
      simp only [run, hd]
      rfl
    obtain ⟨g, hg, hv'⟩ := source_value R z j s v hv
    have he : g = f := Option.some.inj (hg.symm.trans h)
    exact ⟨v, hv, he ▸ hv'⟩

theorem work (n : ℕ) (j : Fin 3) (s : (permutationCoupling n (size n j)).Seed) :
    (run n j s).2 ≤ size n j * n ^ 3 + 10 * (size n j + 1) ^ 2 + 4 * size n j + 3 := by
  have hd := PermutationDigitsExecution.counts n (size n j) s
  unfold run
  dsimp only
  split
  · dsimp only; omega
  next d _ =>
    have hp := PermutationArray.build_work (size n j) d
    dsimp only
    omega

end LowSpaceSubsetSum.PartitionLabelExecution

end

end OAI
