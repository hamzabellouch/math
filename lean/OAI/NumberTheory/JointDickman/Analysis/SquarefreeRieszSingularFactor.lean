import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeSingularFactor

namespace OAI

/-! # The local analytic factor for the squarefree Riesz mean -/
namespace JointDickman
open Filter Finset Asymptotics
open scoped Topology

noncomputable def squarefreeRieszSingularFactor (z : ℝ) (s : ℂ) : ℂ :=
  squarefreeSingularFactor z s / (s+1)

theorem squarefreeRieszSingularFactor_analyticAt_one {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    AnalyticAt ℂ (squarefreeRieszSingularFactor z) 1 := by
  exact (squarefreeSingularFactor_analyticAt_one hz hz1).div
    (analyticAt_id.add analyticAt_const) (by norm_num)

theorem squarefreeRieszSingularFactor_one {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    squarefreeRieszSingularFactor z 1 =
      (squarefreeLeadingConstant z * Real.Gamma z / 2 : ℝ) := by
  rw [squarefreeRieszSingularFactor,squarefreeSingularFactor_one hz hz1]
  push_cast
  norm_num

theorem squarefreeRieszSingularFactor_taylor {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    ∃ a : ℕ → ℂ, a 0 = (squarefreeLeadingConstant z * Real.Gamma z / 2 : ℝ) ∧
      ∀ H : ℕ, (fun w : ℂ => squarefreeRieszSingularFactor z (1+w) -
        ∑ j ∈ range (H+1), a j*w^j) =O[𝓝 0] (fun w : ℂ => ‖w‖^(H+1)) := by
  obtain ⟨p,hp⟩ := squarefreeRieszSingularFactor_analyticAt_one hz.le hz1
  refine ⟨p.coeff,?_,?_⟩
  · exact (hp.coeff_zero (fun _ => 1)).trans (squarefreeRieszSingularFactor_one hz hz1)
  · intro H
    simpa only [FormalMultilinearSeries.partialSum,FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      smul_eq_mul,mul_comm] using hp.isBigO_sub_partialSum_pow (H+1)

end JointDickman

end OAI
