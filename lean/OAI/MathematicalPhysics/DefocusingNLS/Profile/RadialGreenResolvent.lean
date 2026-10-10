import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGreenOperator
import Mathlib.Topology.MetricSpace.Contracting

namespace OAI

/-! The positive inverse of `-Δ-1/2` on the small radial ball. -/

open Set Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem exists_radialGreenResolvent (R : ℝ) (hR : 0 ≤ R) (hR2 : R^2 ≤ 11)
    (f : ℝ →ᵇ ℝ) :
    ∃ u : ℝ →ᵇ ℝ,
      u = radialGreenOperator R hR f+(1/2 : ℝ) • radialGreenOperator R hR u ∧
      ‖u‖ ≤ (22/37 : ℝ)*‖f‖ ∧
      ((∀ r ∈ Icc 0 R, 0 ≤ f r) → ∀ r, 0 ≤ u r) := by
  let K := radialGreenOperator R hR
  have hK (g : ℝ →ᵇ ℝ) : ‖K g‖ ≤ (11/24 : ℝ)*‖g‖ := by
    exact (boundedRadialGreen_norm R hR g).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hR2 (by norm_num)) (norm_nonneg g))
  let P : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ) := fun u => K f+(1/2 : ℝ) • K u
  let c : NNReal := ⟨11/48, by norm_num⟩
  have hP : ContractingWith c P := by
    refine ⟨by change (11/48 : ℝ)<1; norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    change dist (K f+(1/2 : ℝ) • K u) (K f+(1/2 : ℝ) • K v) ≤ _
    rw [dist_eq_norm,add_sub_add_left_eq_sub]
    rw [← smul_sub (1/2 : ℝ) (K u) (K v),← map_sub,norm_smul]
    norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2),NNReal.coe_div,
      NNReal.coe_ofNat,c]
    calc
      (1/2 : ℝ)*‖K (u-v)‖ ≤ (1/2)*((11/24)*‖u-v‖) :=
        mul_le_mul_of_nonneg_left (hK _) (by norm_num)
      _ = (11/48)*dist u v := by rw [dist_eq_norm]; ring
  let u := hP.fixedPoint P
  have hu : P u=u := hP.fixedPoint_isFixedPt
  refine ⟨u,hu.symm,?_,?_⟩
  · have hn : ‖u‖ ≤ (11/24 : ℝ)*‖f‖+(11/48 : ℝ)*‖u‖ := by
      calc
        ‖u‖ = ‖K f+(1/2 : ℝ) • K u‖ := congrArg norm hu.symm
        _ ≤ ‖K f‖+‖(1/2 : ℝ) • K u‖ := norm_add_le _ _
        _ = ‖K f‖+(1/2)*‖K u‖ := by rw [norm_smul]; norm_num
        _ ≤ (11/24)*‖f‖+(1/2)*((11/24)*‖u‖) := by gcongr <;> apply hK
        _ = _ := by ring
    linarith
  · intro hf r
    have hi : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ (P^[n] 0) x := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ n hn =>
        intro x
        rw [Function.iterate_succ_apply']
        change 0 ≤ K f x+(1/2 : ℝ)*K (P^[n] 0) x
        exact add_nonneg (radialGreenOperator_nonneg R hR f hf x)
          (mul_nonneg (by norm_num)
            (radialGreenOperator_nonneg R hR (P^[n] 0) (fun y _ => hn y) x))
    have ht : Tendsto (fun n => (P^[n] 0) r) atTop (𝓝 (u r)) :=
      ((BoundedContinuousFunction.lipschitz_eval_const r).continuous.continuousAt.tendsto).comp (hP.tendsto_iterate_fixedPoint 0)
    exact ge_of_tendsto ht (Eventually.of_forall (fun n => hi n r))

end DefocusingNLS

end OAI
