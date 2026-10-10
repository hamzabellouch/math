import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PartitionArrayExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSamplerExecution

namespace OAI

/-! # Stored balanced partitions with the analyzed sampler law -/

noncomputable section
namespace LowSpaceSubsetSum.StoredPartitions

variable {n : ℕ}

abbrev Data (n : ℕ) := ∀ j : Fin 3, PartitionArrayExecution.Labels n j

def run (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (s : (R.partitionsCoupling z).Seed) : Option (Data n) × ℕ :=
  PartitionArrayExecution.run R z 3 id s

def encode (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (f : R.Partitions z) : Data n :=
  fun j => PartitionArrayExecution.encode R z j (f j)

theorem value (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (s : (R.partitionsCoupling z).Seed) :
    (run R z s).1 = ((R.partitionsCoupling z).bounded s).map (encode R z) := by
  have h := PartitionArrayExecution.value R z 3 id s
  have he : PartitionArrayExecution.execution R z 3 id = R.partitionsExecution z := rfl
  rw [he, (R.partitionsExecution z).value_eq] at h
  exact h

theorem complete (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (s : (R.partitionsCoupling z).Seed) (f : R.Partitions z)
    (h : (R.partitionsCoupling z).bounded s = some f) :
    (run R z s).1 = some (encode R z f) := by
  rw [value, h, Option.map_some]

theorem source (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (s : (R.partitionsCoupling z).Seed) (data : Data n)
    (h : (run R z s).1 = some data) :
    ∃ f, (R.partitionsCoupling z).bounded s = some f ∧
      ∀ (j : Fin 3) (k : Fin (PartitionLabelExecution.size n j)),
        (data j)[k.val] = (f j).val ((CanonicalPartition.ranks R z j).symm k) := by
  rw [value] at h
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨f, hf, ?_⟩
  intro j k
  simp only [encode, PartitionArrayExecution.encode, Vector.getElem_ofFn]

theorem work (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (s : (R.partitionsCoupling z).Seed) :
    (run R z s).2 ≤ 3 * (mixerSize n * n ^ 3 + 10 * (mixerSize n + 1) ^ 2 +
      4 * mixerSize n + 6) + 1 :=
  PartitionArrayExecution.work R z 3 id s

end LowSpaceSubsetSum.StoredPartitions

end

end OAI
