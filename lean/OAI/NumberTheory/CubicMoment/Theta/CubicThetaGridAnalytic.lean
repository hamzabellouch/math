import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKernelAnalytic

namespace OAI

/-! Coordinate analyticity of every actual Eisenstein summand in the
positive upper half-space. -/
noncomputable section
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def CubicThetaCoordinateAnalytic (F : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) : Prop :=
  AnalyticAt ℝ (fun t : ℝ => F t y v) x ∧
    AnalyticAt ℝ (fun t : ℝ => F x t v) y ∧
    AnalyticAt ℝ (fun t : ℝ => F x y t) v

lemma cubicThetaCoordinateAnalytic_congr {F G : ℝ → ℝ → ℝ → ℂ}
    (hFG : ∀ x y v, 0<v → F x y v=G x y v) {x y v : ℝ} (hv : 0<v)
    (hG : CubicThetaCoordinateAnalytic G x y v) : CubicThetaCoordinateAnalytic F x y v := by
  refine ⟨hG.1.congr ?_,hG.2.1.congr ?_,hG.2.2.congr ?_⟩
  · exact Eventually.of_forall (fun t => (hFG t y v hv).symm)
  · exact Eventually.of_forall (fun t => (hFG x t v hv).symm)
  · filter_upwards [eventually_gt_nhds hv] with t ht
    exact (hFG x y t ht).symm

lemma cubicThetaCoordinateAnalytic_translated (s C : ℂ) (a b x y : ℝ)
    {v : ℝ} (hv : 0<v) :
    CubicThetaCoordinateAnalytic
      (fun u w t => C*cubicThetaCartesianKernel s (u+a) (w+b) t) x y v := by
  refine ⟨analyticAt_const.mul ?_,analyticAt_const.mul ?_,analyticAt_const.mul ?_⟩
  · exact (cubicThetaCartesian_x_analytic s (x+a) (y+b) hv).comp (f:=fun t : ℝ => t+a) (x:=x)
      (show AnalyticAt ℝ (fun t : ℝ => t+a) x by fun_prop)
  · exact (cubicThetaCartesian_y_analytic s (x+a) (y+b) hv).comp (f:=fun t : ℝ => t+b) (x:=y)
      (show AnalyticAt ℝ (fun t : ℝ => t+b) y by fun_prop)
  · exact cubicThetaCartesian_v_analytic s (x+a) (y+b) hv

theorem cubicThetaEisensteinGrid_analytic (c d : Eisenstein) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    CubicThetaCoordinateAnalytic
      (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s) x y v := by
  by_cases hc0 : c=0
  · subst c
    simp only [CubicThetaCoordinateAnalytic,cubicThetaEisensteinGridTerm_zero,cubicThetaCartesianPoint]
    by_cases hd : d=1
    · simp only [ite_eq_left hd]
      exact ⟨analyticAt_const,analyticAt_const,cubicThetaHeightPower_analytic s hv⟩
    · simp only [ite_eq_right hd]
      exact ⟨analyticAt_const,analyticAt_const,analyticAt_const⟩
  · by_cases hc : (3:Eisenstein)∣c
    · exact cubicThetaCoordinateAnalytic_congr
        (fun a b t ht => cubicThetaEisensteinGridTerm_cartesian hc hc0 d s a b ht) hv
        (cubicThetaCoordinateAnalytic_translated s
          (cubicThetaEisensteinWeight c d*(norm c:ℂ)^(-s))
          ((d:ℂ)/(c:ℂ)).re ((d:ℂ)/(c:ℂ)).im x y hv)
    · have he : (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s)=
          (fun _ _ _ => (0:ℂ)) := by
        funext a b t
        simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hc]
      rw [he]
      exact ⟨analyticAt_const,analyticAt_const,analyticAt_const⟩

end CubicFirstMoment

end

end OAI
