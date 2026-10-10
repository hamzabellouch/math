import OAI.Analysis.LienardCycles.OvalMatching

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
open ScaledProfile ScalarArcs AxisFlow RealAnalysis GlobalODE
lemma IsLimitCycle.matching {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {C : Set Plane} (hC : IsLimitCycle F C) :
    ∃ r,IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r ∧
      (0,poly a 0+axisM a r+r) ∈ C := by
  obtain ⟨z,S,T,hz,hS,hST,hp,hr,hl,hCz⟩ := hC.1.oval hF
  obtain ⟨hr0,hd0,hb0⟩ := hz.oval_matching hF hp hr hl
  let r0 := ((z 0).2-(z S).2)/2
  let b : ℝ → ℝ := fun r=>poly a 0+axisM a r+r
  change b r0=(z 0).2 at hb0
  obtain ⟨U,hU,hCU,hiso⟩ := hC.2
  have hzU : range z ⊆ U := hCz ▸ hCU
  obtain ⟨R,_,_,_,_,_,hne,hnear⟩ := hz.return_neighborhood hF hS hST hp hr hl
  have hbc : ContinuousAt b r0 :=
    (continuousAt_const.add (axisM_analytic a hr0.1).continuousAt).add continuousAt_id
  have hbt : Tendsto b (𝓝 r0) (𝓝 (z 0).2) := by simpa only [hb0] using hbc.tendsto
  have hne' := hbt.eventually hne
  have hnear' := hbt.eventually (hnear U hU hzU)
  have isolated : ∀ᶠ r in 𝓝 r0,r ∈ matchingDomain a (reflectX a) → matchingDelta a (reflectX a) r=0 → r=r0 := by
    filter_upwards [hne',hnear'] with r hn hu hmem hdelta
    obtain ⟨hs,hst,hR,hL,hlo,hhi,hhi',hW⟩ := hn
    have hfix := R.fixed_of_matching hF hmem hdelta hs hst hR hL hlo hhi hhi' hW
    have hper : Function.Periodic (R.path (b r)) (R.σ (b r)) := flow_periodic_of_hit R.W R.lip R.bound hfix
    have hsol : IsSolution F (R.path (b r)) := flow_true_of_closed R.W R.lip R.bound (hs.trans hst) hfix hW
    have horbit : IsPeriodicOrbit F (range (R.path (b r))) :=
      ⟨R.path (b r),R.σ (b r),hsol,hs.trans hst,hper,hR.nonconstant,rfl⟩
    have hin : range (R.path (b r)) ⊆ U := periodic_range_subset hper (hs.trans hst) hu
    have he : range (R.path (b r))=C := hiso _ horbit hin
    have hstart : ((0,b r):Plane) ∈ range z := by
      rw [←hCz,←he]
      exact ⟨0,R.path_zero _⟩
    have hpoint := hz.oval_axis_positive hS hST hp hr hl hstart rfl hhi
    have hbeq : b r=b r0 := (congrArg Prod.snd hpoint).trans hb0.symm
    have hPeq : axisPeak a r=axisPeak a r0 :=
      (axisUpper_strictMono a).injOn (axisPeak_spec a hmem.1).1 (axisPeak_spec a hr0.1).1
        (by rw [(axisPeak_endpoints hmem.1).2,(axisPeak_endpoints hr0.1).2];exact hbeq)
    calc r=axisWidth a (axisPeak a r) := (axisPeak_spec a hmem.1).2.symm
         _=axisWidth a (axisPeak a r0) := congrArg (axisWidth a) hPeq
         _=r0 := (axisPeak_spec a hr0.1).2
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp isolated
  refine ⟨r0,⟨hr0,hd0,ε,hε,?_⟩,?_⟩
  · intro r hr hmem hd
    apply hball ?_ hmem hd
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith [hr.1,hr.2]
  · rw [hCz]
    refine ⟨0,Prod.ext hr.left ?_⟩
    exact hb0.symm
lemma limitCycle_encard_le_matching {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) :
    {C : Set Plane | IsLimitCycle F C}.encard ≤
      {r | IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r}.encard := by
  classical
  let f : {C : Set Plane // IsLimitCycle F C} → ℝ := fun C=>Classical.choose (C.prop.matching hF)
  have hf (C : {C : Set Plane // IsLimitCycle F C}) :
      IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) (f C) ∧
      (0,poly a 0+axisM a (f C)+f C) ∈ (C : Set Plane) := Classical.choose_spec (C.prop.matching hF)
  have hi : Function.Injective f := by
    intro C D he
    apply Subtype.ext
    exact C.prop.1.eq_of_common D.prop.1 (hf C).2 (by rw [he];exact (hf D).2)
  have hm : Set.MapsTo f univ {r | IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r} :=
    fun C _=>(hf C).1
  have H := Set.encard_le_encard_of_injOn hm hi.injOn
  rw [Set.encard_univ] at H
  exact H
end QuinticLienard

end OAI
