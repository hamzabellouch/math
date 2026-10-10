import OAI.Analysis.LienardCycles.SecantIntegral

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open PartialCalculus QuadraticFit QuadraticCoordinates RealAnalysis
noncomputable def Vm : (ℝ×ℝ)×ℝ → ℝ := direction ((0,0),1) conditionalV
noncomputable def Vk : (ℝ×ℝ)×ℝ → ℝ := direction ((1,0),0) conditionalV
lemma Vm_deriv {k r M : ℝ} (hr : 0<r) (hM : |M|<r) :
    HasDerivAt (fun u=>conditionalV ((k,r),u)) (Vm ((k,r),M)) M := by
  simpa [Vm,direction] using!
    ((conditionalV_analytic hr hM).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt M
      ((hasDerivAt_const M (k,r)).prodMk (hasDerivAt_id M))
lemma Vk_deriv {k r M : ℝ} (hr : 0<r) (hM : |M|<r) :
    HasDerivAt (fun u=>conditionalV ((u,r),M)) (Vk ((k,r),M)) k := by
  simpa [Vk,direction] using!
    ((conditionalV_analytic hr hM).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt k
      (((hasDerivAt_id k).prodMk (hasDerivAt_const k r)).prodMk (hasDerivAt_const k M))
lemma Vk_pos {k r M : ℝ} (hr : 0<r) (hM : |M|<r) : 0<Vk ((k,r),M) := by
  rw [(Vk_deriv hr hM).unique (conditionalV_deriv hr hM)]
  exact div_pos (G_pos hr) (QuadraticVariation.P_pos hr)
lemma abs_segment_lt {r x y s : ℝ} (hx : |x|<r) (hy : |y|<r) (hs : s ∈ Icc 0 1) :
    |y+s*(x-y)|<r := by
  have hx' := abs_lt.mp hx
  have hy' := abs_lt.mp hy
  have hm := (convex_Ioo (-r) r) hy' hx' (sub_nonneg.mpr hs.2) hs.1 (by ring : 1-s+s=1)
  convert! (abs_lt.mpr hm) using 1
  simp only [smul_eq_mul]
  congr 1
  ring
noncomputable def mSegment (a b : Fin 6 → ℝ) (q : ℝ×ℝ) : (ℝ×ℝ)×ℝ :=
  ((axisKappa a q.1,q.1),axisM b q.1+q.2*(axisM a q.1-axisM b q.1))
noncomputable def kSegment (a b : Fin 6 → ℝ) (q : ℝ×ℝ) : (ℝ×ℝ)×ℝ :=
  ((axisKappa b q.1+q.2*(axisKappa a q.1-axisKappa b q.1),q.1),axisM b q.1)
noncomputable def secantA (a b : Fin 6 → ℝ) (r : ℝ) : ℝ := ∫ s : ℝ in (0:ℝ)..1,Vm (mSegment a b (r,s))
noncomputable def secantB (a b : Fin 6 → ℝ) (r : ℝ) : ℝ := ∫ s : ℝ in (0:ℝ)..1,Vk (kSegment a b (r,s))
lemma mSegment_continuousAt {a b : Fin 6 → ℝ} {r s : ℝ} (hr : r ∈ matchingDomain a b) :
    ContinuousAt (mSegment a b) (r,s) := by
  change ContinuousAt (fun q : ℝ×ℝ => ((axisKappa a q.1,q.1),axisM b q.1+q.2*(axisM a q.1-axisM b q.1))) (r,s)
  exact (((axisKappa_analytic a hr.1).continuousAt.comp (x := (r,s)) continuousAt_fst).prodMk continuousAt_fst).prodMk
    (((axisM_analytic b hr.2).continuousAt.comp (x := (r,s)) continuousAt_fst).add
      (continuousAt_snd.mul (((axisM_analytic a hr.1).continuousAt.comp (x := (r,s)) continuousAt_fst).sub
        ((axisM_analytic b hr.2).continuousAt.comp (x := (r,s)) continuousAt_fst))))
lemma kSegment_continuousAt {a b : Fin 6 → ℝ} {r s : ℝ} (hr : r ∈ matchingDomain a b) :
    ContinuousAt (kSegment a b) (r,s) := by
  change ContinuousAt (fun q : ℝ×ℝ => ((axisKappa b q.1+q.2*(axisKappa a q.1-axisKappa b q.1),q.1),axisM b q.1)) (r,s)
  exact ((((axisKappa_analytic b hr.2).continuousAt.comp (x := (r,s)) continuousAt_fst).add
    (continuousAt_snd.mul (((axisKappa_analytic a hr.1).continuousAt.comp (x := (r,s)) continuousAt_fst).sub
      ((axisKappa_analytic b hr.2).continuousAt.comp (x := (r,s)) continuousAt_fst)))).prodMk continuousAt_fst).prodMk
        ((axisM_analytic b hr.2).continuousAt.comp (x := (r,s)) continuousAt_fst)
lemma secant_integrands_continuous {a b : Fin 6 → ℝ} {R : Set ℝ} (hR : R ⊆ matchingDomain a b) :
    ContinuousOn (fun q=>Vm (mSegment a b q)) (R ×ˢ Icc 0 1) ∧
      ContinuousOn (fun q=>Vk (kSegment a b q)) (R ×ˢ Icc 0 1) := by
  constructor
  · intro q hq
    have hr := hR hq.1
    have hM := abs_segment_lt (axisM_abs_lt a hr.1).2 (axisM_abs_lt b hr.2).2 hq.2
    have hv : ContinuousAt Vm (mSegment a b q) :=
      (direction_contDiffAt (conditionalV_analytic (axisM_abs_lt a hr.1).1 hM) ((0,0),1)).continuousAt
    exact (hv.comp (mSegment_continuousAt hr)).continuousWithinAt
  · intro q hq
    have hr := hR hq.1
    have hv : ContinuousAt Vk (kSegment a b q) :=
      (direction_contDiffAt (conditionalV_analytic (axisM_abs_lt b hr.2).1 (axisM_abs_lt b hr.2).2) ((1,0),0)).continuousAt
    exact (hv.comp (kSegment_continuousAt hr)).continuousWithinAt
lemma secantA_continuousOn {a b : Fin 6 → ℝ} {l r : ℝ} (hl : l ∈ matchingDomain a b) (hr : r ∈ matchingDomain a b) :
    ContinuousOn (secantA a b) (Icc l r) :=
  continuousOn_segment_integral (secant_integrands_continuous ((matchingDomain_ordConnected a b).out hl hr)).1
lemma secantB_pos {a b : Fin 6 → ℝ} {r : ℝ} (hr : r ∈ matchingDomain a b) : 0<secantB a b r := by
  have hc : ContinuousOn (fun s=>Vk (kSegment a b (r,s))) (Icc 0 1) :=
    (secant_integrands_continuous (Subset.refl (matchingDomain a b))).2.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun s hs=>⟨hr,hs⟩)
  exact intervalIntegral.integral_pos (by norm_num) hc
    (fun s _=>(Vk_pos (axisM_abs_lt b hr.2).1 (axisM_abs_lt b hr.2).2).le)
    ⟨1/2,by norm_num,Vk_pos (axisM_abs_lt b hr.2).1 (axisM_abs_lt b hr.2).2⟩
lemma secant_identity {a b : Fin 6 → ℝ} {r : ℝ} (hr : r ∈ matchingDomain a b) :
    axisV a r-axisV b r=secantA a b r*(axisM a r-axisM b r)+
      secantB a b r*(axisKappa a r-axisKappa b r) := by
  have hM (s : ℝ) (hs : s ∈ Icc 0 1) := abs_segment_lt (axisM_abs_lt a hr.1).2 (axisM_abs_lt b hr.2).2 hs
  have hdm (s : ℝ) (hs : s ∈ Icc 0 1) : HasDerivAt
      (fun u=>conditionalV (mSegment a b (r,u)))
      (Vm (mSegment a b (r,s))*(axisM a r-axisM b r)) s := by
    simpa [mSegment] using! (Vm_deriv (k := axisKappa a r) (axisM_abs_lt a hr.1).1 (hM s hs)).comp s
      ((hasDerivAt_const s (axisM b r)).add ((hasDerivAt_id s).mul_const (axisM a r-axisM b r)))
  have hdk (s : ℝ) (_hs : s ∈ Icc 0 1) : HasDerivAt
      (fun u=>conditionalV (kSegment a b (r,u)))
      (Vk (kSegment a b (r,s))*(axisKappa a r-axisKappa b r)) s := by
    simpa [kSegment] using! (Vk_deriv (k := axisKappa b r+s*(axisKappa a r-axisKappa b r)) (axisM_abs_lt b hr.2).1 (axisM_abs_lt b hr.2).2).comp s
      ((hasDerivAt_const s (axisKappa b r)).add ((hasDerivAt_id s).mul_const (axisKappa a r-axisKappa b r)))
  have hc := secant_integrands_continuous (Subset.refl (matchingDomain a b))
  have hcm := hc.1.comp (continuous_const.prodMk continuous_id).continuousOn (fun s hs=>⟨hr,hs⟩)
  have hck := hc.2.comp (continuous_const.prodMk continuous_id).continuousOn (fun s hs=>⟨hr,hs⟩)
  have hm := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f:=fun u=>conditionalV (mSegment a b (r,u)))
    (fun s hs=>hdm s (by simpa using hs)) ((hcm.mul_const _).intervalIntegrable_of_Icc (by norm_num))
  have hk := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f:=fun u=>conditionalV (kSegment a b (r,u)))
    (fun s hs=>hdk s (by simpa using hs)) ((hck.mul_const _).intervalIntegrable_of_Icc (by norm_num))
  rw [intervalIntegral.integral_mul_const] at hm hk
  simp only [mSegment,kSegment,zero_mul,add_zero,one_mul,add_sub_cancel] at hm hk
  rw [axisV_conditional a hr.1,axisV_conditional b hr.2]
  change _=secantA a b r*(axisM a r-axisM b r)+secantB a b r*(axisKappa a r-axisKappa b r)
  change secantA a b r*(axisM a r-axisM b r)=_ at hm
  change secantB a b r*(axisKappa a r-axisKappa b r)=_ at hk
  linarith
end QuinticLienard.AxisFlow

end OAI
