import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitial

namespace OAI

/-! The literal odd subdivision satisfies all hypotheses needed to iterate
the full-space fork estimate. Its fresh singlets have distinct endpoints. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

theorem initial_background_valid (n : ℕ) (bs : List Bond) (c N : ℚ) :
    SourceBondLists.bounded (initial n bs c N).1 (background (initial n bs c N)) ∧
      ∀ b ∈ background (initial n bs c N), b.1 ≠ b.2.1 := by
  have hv : ∀ b ∈ background (initial n bs c N),
      b.1 < (initial n bs c N).1 ∧ b.2.1 < (initial n bs c N).1 ∧ b.1 ≠ b.2.1 := by
    intro b hb
    rcases List.mem_append.mp hb with hs | hp
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hs
      have he' := List.mem_range.mp he
      dsimp only [initial]
      omega
    · exact unpairedBonds_valid (initial_validPorts n bs c N) b hp
  exact ⟨fun b hm => ⟨(hv b hm).1,(hv b hm).2.1⟩,fun b hm => (hv b hm).2.2⟩

theorem initial_iterate_accuracy (n : ℕ) (bs : List Bond) (c N : ℚ) (hN : 0 < N)
    (k : ℕ) :
    |MediatorGraph.normalizedBottom (matrix (iterate N k (initial n bs c N)))-
      MediatorGraph.normalizedBottom (matrix (initial n bs c N))| ≤ (k:ℝ)/(N:ℝ) := by
  have h := initial_background_valid n bs c N
  exact iterate_accuracy _ (initial_validPorts n bs c N) h.1 h.2 N hN k

end ContinuumCoulomb.QuantumForkList

end

end OAI
