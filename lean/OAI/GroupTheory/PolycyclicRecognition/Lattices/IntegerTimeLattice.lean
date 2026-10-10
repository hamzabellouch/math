import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeMetric
import Mathlib.Topology.Instances.ZMultiples
import Mathlib.Algebra.Group.TypeTags.Basic

namespace OAI

/-! # The integer time lattice in the real one-parameter group -/

noncomputable section
namespace PolycyclicRecognition
open Set

def integerTimeLattice : Subgroup (Multiplicative ℝ) :=
  (AddSubgroup.zmultiples (1 : ℝ)).toSubgroup

theorem integerTimeLattice_mem (n : ℤ) :
    Multiplicative.ofAdd (n : ℝ) ∈ integerTimeLattice := by
  change (n : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ)
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp⟩

theorem integerTimeLattice_exists {x : Multiplicative ℝ} (hx : x ∈ integerTimeLattice) :
    ∃ n : ℤ, x = Multiplicative.ofAdd (n : ℝ) := by
  change x.toAdd ∈ AddSubgroup.zmultiples (1 : ℝ) at hx
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  refine ⟨n, ?_⟩
  apply Multiplicative.ext
  simpa using hn.symm

theorem integerTimeLattice_uniform : IsUniformLattice integerTimeLattice := by
  have hd : DiscreteTopology integerTimeLattice := by
    change DiscreteTopology (AddSubgroup.zmultiples (1 : ℝ))
    infer_instance
  refine ⟨hd, Multiplicative.ofAdd '' Icc (0 : ℝ) 1,
    isCompact_Icc.image (show Continuous (Multiplicative.ofAdd : ℝ → Multiplicative ℝ)
      from continuous_id), ?_⟩
  intro x
  refine ⟨⟨Multiplicative.ofAdd (⌊x.toAdd⌋ : ℝ), integerTimeLattice_mem _⟩,
    Multiplicative.ofAdd (Int.fract x.toAdd), ?_, ?_⟩
  · exact ⟨Int.fract x.toAdd, ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩
  · apply Multiplicative.ext
    change (⌊x.toAdd⌋ : ℝ) + (x.toAdd - (⌊x.toAdd⌋ : ℝ)) = x.toAdd
    abel

end PolycyclicRecognition

end

end OAI
