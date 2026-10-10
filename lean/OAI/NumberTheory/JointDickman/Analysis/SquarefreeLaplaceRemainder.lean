import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeTaylor
import OAI.NumberTheory.JointDickman.Analysis.LaplaceRemainder

namespace OAI

/-! # Integrating the actual singular-factor Taylor remainders -/
namespace JointDickman
open Filter Finset MeasureTheory Set
open scoped Topology

 theorem squarefreeSingularFactor_laplace_remainders {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ a : ℕ → ℂ, a 0 = (squarefreeLeadingConstant z*Real.Gamma z : ℝ) ∧
      ∀ H : ℕ, ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ ∀ L : ℝ, 0 < L →
        ‖∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
          (squarefreeSingularFactor z (1-(t:ℂ)) - ∑ j ∈ range (H+1), a j*(-(t:ℂ))^j)‖ ≤
          C*L^(z-H-2)*Real.Gamma ((H:ℝ)+2-z) := by
  obtain ⟨a,ha,htaylor⟩ := squarefreeSingularFactor_taylor hz hz1.le
  refine ⟨a,ha,fun H => ?_⟩
  obtain ⟨C,hC,hbound⟩ := (htaylor H).exists_pos
  obtain ⟨ε,hε,hεbound⟩ := Metric.eventually_nhds_iff.mp hbound.bound
  refine ⟨C,ε/2,hC,by linarith,fun L hL => ?_⟩
  have hb (t : ℝ) (ht : t ∈ Ioc 0 (ε/2)) :
      ‖squarefreeSingularFactor z (1-(t:ℂ)) - ∑ j ∈ range (H+1), a j*(-(t:ℂ))^j‖ ≤ C*t^(H+1) := by
    have hd : dist (-(t:ℂ)) 0 < ε := by
      rw [dist_zero_right,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1]
      linarith [ht.2]
    have hh := hεbound hd
    simpa [sub_eq_add_neg,Complex.norm_real,abs_of_pos ht.1] using hh
  have h := laplace_remainder_bound hz1 hL hC.le (H+1)
    (fun t => squarefreeSingularFactor z (1-(t:ℂ)) - ∑ j ∈ range (H+1), a j*(-(t:ℂ))^j) hb
  simpa only [Nat.cast_add,Nat.cast_one,
    show z-((H:ℝ)+1)-1 = z-H-2 by ring,
    show (H:ℝ)+1+1-z = (H:ℝ)+2-z by ring] using h

end JointDickman

end OAI
