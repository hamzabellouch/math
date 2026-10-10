import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridMajorant
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateAxis

namespace OAI

/-! Each coordinate line has a neighborhood with uniformly positive
height and a bounded Eisenstein majorant constant. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaHeightBudget_continuousAt {p : ℝ → ℂ × ℝ} {t : ℝ}
    (hp : ContinuousAt p t) (ht : 0<(p t).2) :
    ContinuousAt (fun w => (p w).2*cubicThetaHeightConstant (p w)) t := by
  unfold cubicThetaHeightConstant
  have hn : (p t).2^2≠0 := pow_ne_zero _ ht.ne'
  fun_prop

lemma cubicThetaCoordinate_local_budget (k : CubicThetaAxis) (x y : ℝ)
    {v : ℝ} (hv : 0<v) :
    ∃ r : ℝ, 0<r ∧ ∀ t ∈ Set.Ioo
      (cubicThetaCoordinateCenter k x y v-r) (cubicThetaCoordinateCenter k x y v+r),
      v/2 < (cubicThetaCoordinateLine k x y v t).2 ∧
      (cubicThetaCoordinateLine k x y v t).2*
        cubicThetaHeightConstant (cubicThetaCoordinateLine k x y v t) <
          v*cubicThetaHeightConstant (cubicThetaCartesianPoint x y v)+1 := by
  let w := cubicThetaCoordinateCenter k x y v
  let p := cubicThetaCoordinateLine k x y v
  have hp : ContinuousAt p w := (cubicThetaCoordinateLine_continuous k x y v).continuousAt
  have hp0 : (p w).2=v := congrArg Prod.snd (cubicThetaCoordinateLine_center k x y v)
  have he1 : ∀ᶠ t in 𝓝 w, v/2<(p t).2 := hp.snd.eventually_const_lt (by change v/2<(p w).2; rw [hp0]; linarith)
  have he2 : ∀ᶠ t in 𝓝 w, (p t).2*cubicThetaHeightConstant (p t)<
      v*cubicThetaHeightConstant (cubicThetaCartesianPoint x y v)+1 := by
    apply (cubicThetaHeightBudget_continuousAt hp (by rw [hp0]; exact hv)).eventually_lt_const
    dsimp [p,w]
    rw [cubicThetaCoordinateLine_center]
    change v*cubicThetaHeightConstant (cubicThetaCartesianPoint x y v)<
      v*cubicThetaHeightConstant (cubicThetaCartesianPoint x y v)+1
    linarith
  obtain ⟨r,hr,hbound⟩ := Metric.eventually_nhds_iff.mp (he1.and he2)
  refine ⟨r,hr,?_⟩
  intro t ht
  apply hbound
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩

end CubicFirstMoment

end

end OAI
