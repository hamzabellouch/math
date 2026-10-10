import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeTaylor
import OAI.NumberTheory.JointDickman.Analysis.LaplaceTaylor

namespace OAI

/-! # The full local Laplace expansion of the squarefree singular factor -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics Finset
open scoped Topology

theorem squarefreeSingularFactor_laplace_expansion {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ a : ℕ → ℂ, a 0 = (squarefreeLeadingConstant z*Real.Gamma z : ℝ) ∧
      ∀ H : ℕ, ∃ η : ℝ, 0 < η ∧
        (fun L : ℝ => (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
          squarefreeSingularFactor z (1-(t:ℂ))) -
          ∑ j ∈ range (H+1), (L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) •
            (a j*(-1:ℂ)^j)) =O[atTop] (fun L => L^(z-H-2)) := by
  obtain ⟨a,ha,htaylor⟩ := squarefreeSingularFactor_taylor hz hz1.le
  refine ⟨a,ha,fun H => ?_⟩
  obtain ⟨C,hC,hbound⟩ := (htaylor H).exists_pos
  obtain ⟨ε,hε,hεbound⟩ := Metric.eventually_nhds_iff.mp hbound.bound
  obtain ⟨δ,hδ,hδbound⟩ := Metric.eventually_nhds_iff.mp
    (squarefreeSingularFactor_analyticAt_one hz.le hz1.le).eventually_continuousAt
  let η := min ε δ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hdist (t : ℝ) (ht : t ∈ Ioc 0 η) : t < min ε δ := by
    have hm : 0 < min ε δ := lt_min hε hδ
    dsimp [η] at ht
    linarith [ht.2]
  have hf : ContinuousOn (fun t : ℝ => squarefreeSingularFactor z (1-(t:ℂ))) (Ioc 0 η) := by
    intro t ht
    have hd : dist (1-(t:ℂ)) 1 < δ := by
      rw [dist_eq_norm,sub_sub_cancel_left,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1]
      exact (hdist t ht).trans_le (min_le_right _ _)
    have hK : ContinuousAt (squarefreeSingularFactor z) (1-(t:ℂ)) := hδbound hd
    have hi : ContinuousAt (fun u : ℝ => (1:ℂ)-(u:ℂ)) t :=
      continuousAt_const.sub Complex.continuous_ofReal.continuousAt
    exact (ContinuousAt.comp (f := fun u : ℝ => (1:ℂ)-(u:ℂ)) hK hi).continuousWithinAt
  refine ⟨η,hη,laplace_taylor_isBigO hz1 hη hC.le _
    (hf.aestronglyMeasurable measurableSet_Ioc) (fun j => a j*(-1:ℂ)^j) H ?_⟩
  intro t ht
  have hd : dist (-(t:ℂ)) 0 < ε := by
    rw [dist_zero_right,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1]
    exact (hdist t ht).trans_le (min_le_left _ _)
  have hh := hεbound hd
  have hp : (∑ j ∈ range (H+1), a j*(-(t:ℂ))^j) =
      ∑ j ∈ range (H+1), (a j*(-1:ℂ)^j)*(t:ℂ)^j := by
    apply sum_congr rfl
    intro j _
    rw [neg_eq_neg_one_mul,mul_pow,mul_assoc]
  simpa only [hp,sub_eq_add_neg,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1,
    abs_of_nonneg (pow_nonneg ht.1.le _)] using hh

end JointDickman

end OAI
