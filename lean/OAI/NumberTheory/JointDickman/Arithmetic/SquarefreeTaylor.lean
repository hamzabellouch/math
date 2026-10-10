import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeSingularFactor

namespace OAI

/-! # Fixed-order Taylor control of the squarefree singular factor -/
namespace JointDickman
open Filter Finset Asymptotics
open scoped Topology

 theorem squarefreeSingularFactor_taylor {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    ∃ a : ℕ → ℂ, a 0 = (squarefreeLeadingConstant z * Real.Gamma z : ℝ) ∧
      ∀ H : ℕ, (fun w : ℂ => squarefreeSingularFactor z (1+w) -
        ∑ j ∈ range (H+1), a j*w^j) =O[𝓝 0] (fun w : ℂ => ‖w‖^(H+1)) := by
  obtain ⟨p,hp⟩ := squarefreeSingularFactor_hasPowerSeries hz.le hz1
  refine ⟨p.coeff,?_,?_⟩
  · exact (hp.coeff_zero (fun _ => 1)).trans (squarefreeSingularFactor_one hz hz1)
  · intro H
    simpa only [FormalMultilinearSeries.partialSum,FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      smul_eq_mul,mul_comm] using hp.isBigO_sub_partialSum_pow (H+1)

end JointDickman

end OAI
