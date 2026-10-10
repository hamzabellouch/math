import OAI.Analysis.KadisonKastler.ModularRightAction
import OAI.Analysis.KadisonKastler.ScalingCoisometryEstimates
import Mathlib.Topology.MetricSpace.Equicontinuity

namespace OAI

/-! # Extending central modular defects from a cyclic reference vector

Uniform contractivity and centrality extend the scaling equation to every
vector in the same modular representation.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

theorem scaling_defect_tendsto_of_cyclic (d : ModularConjugationData M Ω)
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (v : ℕ → Algebra M) (hv : ∀ n, v n*star (v n)=1) (t : ℂ)
    (hcentral : ∀ a : Algebra M,
      Tendsto (fun n => (v n*a-a*v n).val Ω) atTop (𝓝 0))
    (hΩ : Tendsto (fun n => (v n).val Ω-t • d.rightAction (v n) Ω) atTop (𝓝 0))
    (ξ : H) :
    Tendsto (fun n => (v n).val ξ-t • d.rightAction (v n) ξ) atTop (𝓝 0) := by
  let T (n : ℕ) : H →L[ℂ] H := (v n).val-t • d.rightAction (v n)
  have hn (n : ℕ) : ‖(v n).val‖ ≤ 1 := coisometry_norm_le (v n) (hv n)
  have hR (n : ℕ) : ‖d.rightAction (v n)‖ ≤ 1 := by
    rw [d.rightAction_norm]
    exact hn n
  have hbound (n : ℕ) : ‖T n‖ ≤ 1+‖t‖ := by
    calc
      _ ≤ ‖(v n).val‖+‖t • d.rightAction (v n)‖ := norm_sub_le _ _
      _ = ‖(v n).val‖+‖t‖*‖d.rightAction (v n)‖ := by rw [norm_smul]
      _ ≤ 1+‖t‖*1 := add_le_add (hn n)
        (mul_le_mul_of_nonneg_left (hR n) (norm_nonneg _))
      _ = _ := by rw [mul_one]
  have hequi : Equicontinuous (fun n : ℕ => (T n : H → H)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun s : ℝ => (1+‖t‖)*s)
      (by simpa only [mul_zero] using
        (tendsto_const_nhds.mul tendsto_id :
          Tendsto (fun s : ℝ => (1+‖t‖)*s) (𝓝 0) (𝓝 ((1+‖t‖)*0))))
    intro x y n
    rw [dist_eq_norm,dist_eq_norm,← map_sub]
    exact ((T n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))
  change Tendsto (fun n => T n ξ) atTop (𝓝 0)
  refine hcyc.induction_on (p := fun x => Tendsto (fun n => T n x) atTop (𝓝 0)) ξ ?_ ?_
  · exact hequi.isClosed_setOfPred_tendsto
      (continuous_const : Continuous (fun _ : H => (0 : H)))
  intro a
  have he (n : ℕ) : T n (a.val Ω) =
      (v n*a-a*v n).val Ω+a.val ((v n).val Ω-t • d.rightAction (v n) Ω) := by
    have hc := congrArg (fun A : H →L[ℂ] H => A Ω) (d.rightAction_commute a (v n))
    change a.val (d.rightAction (v n) Ω)=d.rightAction (v n) (a.val Ω) at hc
    change (v n).val (a.val Ω)-t • d.rightAction (v n) (a.val Ω)=
      ((v n).val (a.val Ω)-a.val ((v n).val Ω))+
        a.val ((v n).val Ω-t • d.rightAction (v n) Ω)
    rw [map_sub,map_smul,hc]
    abel
  have ha := (a.val.continuous.tendsto (0 : H)).comp hΩ
  have ht := (hcentral a).add ha
  change Tendsto (fun n => T n (a.val Ω)) atTop (𝓝 0)
  simpa only [he,map_zero,add_zero,Function.comp_def] using ht

end ModularConjugationData

end

end KadisonKastler

end OAI
