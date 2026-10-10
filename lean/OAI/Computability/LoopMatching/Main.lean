import OAI.Computability.LoopMatching.MachineMain
import OAI.Computability.LoopMatching.ExpandCount
import OAI.Computability.LoopMatching.SparseBoundary

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching

theorem actual_algorithm_correct (G : Input) :
    0 < (MachineMain.A G).2 ∧
    (MachineMain.A G).1 ≤ (MachineMain.A G).2 * count G ∧
    (MachineMain.A G).2 * count G ≤ 2 ^ (18 * G.n) * (MachineMain.A G).1 ∧
    ((MachineMain.A G).1 = 0 ↔ count G = 0) := by
  by_cases h : 2 * G.ordinary.records.length + G.loops.length < G.n
  · have hz := count_eq_zero_of_sparse_bound G h
    simp [MachineMain.A, h, hz]
  · rw [MachineMain.A, ite_eq_right h]
    exact ⟨Approximation.output_den_pos G,
      Approximation.output_bounds_of_expanded_count G
        (fun j _ => expanded_count G j)⟩

theorem fullEndpoint : FullEndpoint := by
  obtain ⟨machine, hfinite, hlength⟩ := MachineMain.computational_endpoint
  exact ⟨MachineMain.A, machine, hfinite, hlength, actual_algorithm_correct⟩

end LoopMatching

end OAI
