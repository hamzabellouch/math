import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListNextDegree
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialDegree

namespace OAI

/-! Persistent degree bounds along the actual list iteration. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

theorem next_ordinary_bounded (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) :
    SourceBondLists.bounded (next N s).1 (next N s).2.1 := by
  intro b hm
  change b ∈ s.2.1++addedBonds s (scale N s) at hm
  rcases List.mem_append.mp hm with ho | ha
  · have h := hb b ho
    change b.1<s.1+2*pairCount s.2.2.2 ∧ b.2.1<s.1+2*pairCount s.2.2.2
    exact ⟨lt_of_lt_of_le h.1 (Nat.le_add_right _ _),lt_of_lt_of_le h.2 (Nat.le_add_right _ _)⟩
  · have h := addedBonds_valid s hs (scale N s) b ha
    exact ⟨h.1,h.2.1⟩

theorem iterate_ordinary_bounded (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (k : ℕ) :
    SourceBondLists.bounded (iterate N k s).1 (iterate N k s).2.1 := by
  induction k with
  | zero => exact hb
  | succ k ih => exact next_ordinary_bounded N _ (iterate_validPorts N s hs k) ih

theorem iterate_degreeBounds (N : ℚ) (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 s.2.1) (hd : DegreeBounds s) (k : ℕ) :
    DegreeBounds (iterate N k s) := by
  induction k with
  | zero => exact hd
  | succ k ih =>
    exact next_degreeBounds N _ (iterate_validPorts N s hs k)
      (iterate_ordinary_bounded N s hs hb k) ih

theorem initial_ordinary_bounded (n : ℕ) (bs : List Bond) (c N : ℚ) :
    SourceBondLists.bounded (initial n bs c N).1 (initial n bs c N).2.1 := by
  intro b hb
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
  have he' := List.mem_range.mp he
  change n+2*e<n+2*bs.length ∧ n+2*e+1<n+2*bs.length
  constructor <;> omega

theorem initial_iterate_degreeBounds (n : ℕ) (bs : List Bond) (c N : ℚ) (k : ℕ) :
    DegreeBounds (iterate N k (initial n bs c N)) :=
  iterate_degreeBounds N _ (initial_validPorts n bs c N)
    (initial_ordinary_bounded n bs c N) (initial_degreeBounds n bs c N) k

end ContinuumCoulomb.QuantumForkList

end

end OAI
