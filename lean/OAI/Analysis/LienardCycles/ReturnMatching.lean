import OAI.Analysis.LienardCycles.LocalExcursion

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow GlobalODE
lemma axisPeak_endpoints {a : Fin 6 → ℝ} {r : ℝ} (hr : r ∈ axisWidths a) :
    axisEndpoint a false (axisPeak a r)=poly a 0+axisM a r-r ∧
    axisEndpoint a true (axisPeak a r)=poly a 0+axisM a r+r := by
  have hw := (axisPeak_spec a hr).2
  dsimp [axisWidth] at hw
  dsimp [axisM,axisCenter]
  constructor <;> linarith
lemma ReturnFlow.fixed_of_matching {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) (R : ReturnFlow) {r : ℝ}
    (hr : r ∈ matchingDomain a (reflectX a)) (hd : matchingDelta a (reflectX a) r=0)
    (hs : 0<R.τ (poly a 0+axisM a r+r)) (hST : R.τ (poly a 0+axisM a r+r)<R.σ (poly a 0+axisM a r+r))
    (hR : IsRightExcursion (R.path (poly a 0+axisM a r+r)) 0 (R.τ (poly a 0+axisM a r+r)))
    (hL : IsRightExcursion (QuinticLienard.reverseX (R.path (poly a 0+axisM a r+r)))
      (-R.σ (poly a 0+axisM a r+r)) (-R.τ (poly a 0+axisM a r+r)))
    (hlo : (R.path (poly a 0+axisM a r+r) (R.τ (poly a 0+axisM a r+r))).2<F.eval 0)
    (hhi : F.eval 0<poly a 0+axisM a r+r)
    (hhi' : F.eval 0<(R.path (poly a 0+axisM a r+r) (R.σ (poly a 0+axisM a r+r))).2)
    (hW : ∀ t ∈ Icc 0 (R.σ (poly a 0+axisM a r+r)),R.W (R.path (poly a 0+axisM a r+r) t)=vectorField F (R.path (poly a 0+axisM a r+r) t)) :
    R.path (poly a 0+axisM a r+r) (R.σ (poly a 0+axisM a r+r))=(0,poly a 0+axisM a r+r) := by
  let b := poly a 0+axisM a r+r
  have hpc : Continuous (R.path b) := R.continuous.comp (continuous_const.prodMk continuous_id)
  have hpd (t : ℝ) (ht : t ∈ Icc 0 (R.σ b)) : HasDerivAt (R.path b) (vectorField F (R.path b t)) t := by
    have H := flow_deriv R.W R.lip R.bound (0,b) t
    rw [show R.W (flow R.W R.lip R.bound (0,b) t)=vectorField F (R.path b t) from hW t ht] at H
    exact H
  obtain ⟨H,hH,hHa,hHb⟩ := hR.axis_peak_on hF hpc
    (fun t ht=>hpd t ⟨ht.1,ht.2.trans hST.le⟩) hlo (by simpa using hhi)
  have hPH := axisPeak_endpoints hr.1
  have hPK := axisPeak_endpoints hr.2
  have hHeq : H=axisPeak a r := (axisUpper_strictMono a).injOn hH (axisPeak_spec a hr.1).1 (by simpa [b] using hHb.trans (by simpa [b] using hPH.2.symm))
  have ha : (R.path b (R.τ b)).2=poly a 0+axisM a r-r := by rw [←hHa,hHeq,hPH.1]
  have hM : axisM a r=axisM (reflectX a) r := sub_eq_zero.mp hd
  have hzero : poly (reflectX a) 0=poly a 0 := by simp [reflectX_poly]
  have hzc : Continuous (QuinticLienard.reverseX (R.path b)) :=
    (hpc.fst.comp continuous_neg).neg.prodMk (hpc.snd.comp continuous_neg)
  have hzd (t : ℝ) (ht : t ∈ Icc (-R.σ b) (-R.τ b)) :
      HasDerivAt (QuinticLienard.reverseX (R.path b))
        (vectorField (polynomialReflect F) (QuinticLienard.reverseX (R.path b) t)) t := by
    have hv : -t ∈ Icc 0 (R.σ b) := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have hd0 := (hpd (-t) hv).scomp t (hasDerivAt_id t).neg
    have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd0
    have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd0
    convert! hx.neg.prodMk hy using 1; simp [QuinticLienard.reverseX,vectorField]
  obtain ⟨K,hK,hKa,hKb⟩ := hL.axis_peak_on (a:=reflectX a)
    (fun x=>by rw [polynomialReflect_eval,hF,reflectX_poly]) hzc hzd
    (by simpa [QuinticLienard.reverseX] using hlo) (by simpa [QuinticLienard.reverseX] using hhi')
  simp only [QuinticLienard.reverseX,neg_neg] at hKa hKb
  have hKeq : K=axisPeak (reflectX a) r := (axisLower_strictAnti (reflectX a)).injOn hK (axisPeak_spec _ hr.2).1
    (by rw [hKa,ha,hPK.1,hzero,hM])
  apply Prod.ext
  · have hx := hL.left
    simpa [QuinticLienard.reverseX] using congrArg Neg.neg hx
  · rw [←hKb,hKeq,hPK.2,hzero,←hM]
end QuinticLienard

end OAI
