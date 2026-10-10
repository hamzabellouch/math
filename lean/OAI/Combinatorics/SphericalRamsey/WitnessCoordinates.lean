import OAI.Combinatorics.SphericalRamsey.WitnessScalars
import Mathlib.Tactic.FinCases

namespace OAI

noncomputable section
namespace GrahamSpherical

theorem vertex_injective : Function.Injective vertex := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrArg (fun x : Point 2 => x 0) h
  have h1 := congrArg (fun x : Point 2 => x 1) h
  have hp := v_pos
  have hpu := u_pos
  have hlt := v_lt_u
  have hu := u_lt_one
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals norm_num [vertex, coordinates, squareCoordinate, Fin.ext_iff] at h0
  all_goals norm_num [vertex, coordinates, squareCoordinate, Fin.ext_iff] at h1
  all_goals first | rfl | linarith

theorem vertex_norm (i : Label) : ‖vertex i‖ = 1 := by
  have hs : ‖vertex i‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rcases i with ⟨a,b⟩
    fin_cases a <;> fin_cases b <;>
      simp [vertex, coordinates, squareCoordinate, Fin.ext_iff, Fin.sum_univ_two, u_sq_add_v_sq,
        add_comm (v ^ 2) (u ^ 2)]
  nlinarith [norm_nonneg (vertex i)]

theorem witness_subset_sphere : witness ⊆ Metric.sphere (0 : Point 2) 1 := by
  rintro x ⟨i, rfl⟩
  simpa [Metric.mem_sphere, dist_zero_right] using vertex_norm i

theorem witness_ncard : witness.ncard = 12 := by
  rw [witness, Set.ncard_range_of_injective vertex_injective]
  norm_num [Label]

end GrahamSpherical

end

end OAI
