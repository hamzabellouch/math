import Mathlib
import OAI.Analysis.BiholderTransport.LocalFlow.MIntegralCurveUniformInvariant

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [HasContDiffBump E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

lemma exists_smooth_local_manifold_flow {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞
      (fun x => (⟨x,v x⟩ : TangentBundle I M))) (a : M) :
    ∃ r : ℝ, 0 < r ∧ ∃ U : Set M, IsOpen U ∧ a ∈ U ∧
      ∃ Φ : ℝ × M → M,
        ContMDiffOn (𝓘(ℝ,ℝ).prod I) I ∞ Φ (Ioo (-r) r ×ˢ U) ∧
        (∀ x ∈ U, Φ (0,x) = x) ∧
        (∀ x ∈ U, IsMIntegralCurveOn (fun t => Φ (t,x)) v (Ioo (-r) r)) := by
  let c := extChartAt I a
  obtain ⟨r,hr,_,Ψ,hΨ,hΨ0,hΨder⟩ := exists_smooth_local_flow_on
    (isOpen_extChartAt_target a) (contDiffOn_coordinate_vectorField hv a)
      (c.map_source (mem_extChartAt_source a))
  let U := c.source ∩ c ⁻¹' Metric.ball (c a) r
  have hU : IsOpen U := isOpen_extChartAt_preimage' a Metric.isOpen_ball
  have ha : a ∈ U := ⟨mem_extChartAt_source a,Metric.mem_ball_self hr⟩
  let Φ : ℝ × M → M := fun z => c.symm (Ψ (z.1,c z.2))
  refine ⟨r,hr,U,hU,ha,Φ,?_,?_,?_⟩
  · intro z hz
    have hc : ContMDiffAt I 𝓘(ℝ,E) ∞ c z.2 :=
      (contMDiffOn_extChartAt (I := I) (n := ∞) (x := a)).contMDiffAt
        (by simpa only [extChartAt_source] using
          (isOpen_extChartAt_source (I := I) a).mem_nhds hz.2.1)
    have hg : ContDiffAt ℝ ∞ Ψ (z.1,c z.2) :=
      hΨ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds ⟨hz.1,hz.2.2⟩)
    have hsym : ContMDiffAt 𝓘(ℝ,E) I ∞ c.symm (Ψ (z.1,c z.2)) :=
      (contMDiffOn_extChartAt_symm a).contMDiffAt
        ((isOpen_extChartAt_target a).mem_nhds (hΨder z.1 hz.1 (c z.2) hz.2.2).1)
    have hpair : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ × E) ∞
        (fun w : ℝ × M => (w.1,c w.2)) z :=
      contMDiffAt_prod_module_iff _ |>.mpr ⟨contMDiffAt_fst,hc.comp z contMDiffAt_snd⟩
    exact (hsym.comp z (hg.contMDiffAt.comp z hpair)).contMDiffWithinAt
  · intro x hx
    simp only [Φ,hΨ0 _ hx.2,c.left_inv hx.1]
  · intro x hx t ht
    exact (hasMFDerivAt_of_chart_ode a (hΨder t ht (c x) hx.2).1
      (hΨder t ht (c x) hx.2).2).hasMFDerivWithinAt

end
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [HasContDiffBump E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]
  {v : (x : M) → TangentSpace I x}

variable (hc : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)

omit [CompleteSpace E] [HasContDiffBump E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
noncomputable def completeFlow (t : ℝ) (x : M) : M := Classical.choose (hc x) t

omit [CompleteSpace E] [HasContDiffBump E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
lemma completeFlow_zero (x : M) : completeFlow hc 0 x = x := (Classical.choose_spec (hc x)).1

omit [CompleteSpace E] [HasContDiffBump E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
lemma completeFlow_curve (x : M) : IsMIntegralCurve (fun t => completeFlow hc t x) v :=
  (Classical.choose_spec (hc x)).2

variable (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞ (fun x => (⟨x,v x⟩ : TangentBundle I M)))
include hv

omit [CompleteSpace E] [HasContDiffBump E] in
lemma completeFlow_add (s t : ℝ) (x : M) :
    completeFlow hc (s+t) x = completeFlow hc s (completeFlow hc t x) := by
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (hv.of_le (by simp)) ((completeFlow_curve hc x).comp_add t)
    (completeFlow_curve hc (completeFlow hc t x))
    (by simpa only [Function.comp_apply,zero_add] using
      (completeFlow_zero hc (completeFlow hc t x)).symm)
  exact congrFun he s

omit [CompleteSpace E] [HasContDiffBump E] in
lemma completeFlow_eq_local {r : ℝ} (hr : 0 < r) {U : Set M} {Φ : ℝ × M → M}
    (hΦ0 : ∀ x ∈ U, Φ (0,x) = x)
    (hΦode : ∀ x ∈ U, IsMIntegralCurveOn (fun t => Φ (t,x)) v (Ioo (-r) r))
    {x : M} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-r) r) :
    completeFlow hc t x = Φ (t,x) := by
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) ⟨neg_lt_zero.mpr hr,hr⟩ (hv.of_le (by simp))
    ((completeFlow_curve hc x).isMIntegralCurveOn _) (hΦode x hx) _ ht
  exact (completeFlow_zero hc x).trans (hΦ0 x hx).symm

omit [CompleteSpace E] [HasContDiffBump E] in
lemma completeFlow_smooth_step {r : ℝ} (hr : 0 < r) {U : Set M} (hU : IsOpen U)
    {Φ : ℝ × M → M}
    (hΦ : ContMDiffOn (𝓘(ℝ,ℝ).prod I) I ∞ Φ (Ioo (-r) r ×ˢ U))
    (hΦ0 : ∀ x ∈ U, Φ (0,x) = x)
    (hΦode : ∀ x ∈ U, IsMIntegralCurveOn (fun t => Φ (t,x)) v (Ioo (-r) r))
    {s t : ℝ} {a : M} (hs : ContMDiffAt I I ∞ (completeFlow hc s) a)
    (ha : completeFlow hc s a ∈ U) (ht : t-s ∈ Ioo (-r) r) :
    ContMDiffAt I I ∞ (completeFlow hc t) a := by
  have hsm := (hΦ.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨ht,ha⟩)).comp a
    (contMDiffAt_const.prodMk hs)
  apply hsm.congr_of_eventuallyEq
  have hnear := hs.continuousAt.preimage_mem_nhds (hU.mem_nhds ha)
  filter_upwards [hnear] with x hx
  change completeFlow hc t x = Φ (t-s,completeFlow hc s x)
  rw [← completeFlow_eq_local hc hv hr hΦ0 hΦode hx ht,← completeFlow_add hc hv,sub_add_cancel]

lemma contMDiff_completeFlow_time_slice (t : ℝ) : ContMDiff I I ∞ (completeFlow hc t) := by
  intro a
  let T : Set ℝ := {s | ContMDiffAt I I ∞ (completeFlow hc s) a}
  have hT0 : 0 ∈ T := by
    change ContMDiffAt I I ∞ (completeFlow hc 0) a
    have hzero : completeFlow hc 0 = id := funext (completeFlow_zero hc)
    rw [hzero]
    exact contMDiffAt_id
  have hopen : IsOpen T := by
    apply Metric.isOpen_iff.mpr
    intro s hs
    obtain ⟨r,hr,U,hU,hUa,Φ,hΦ,hΦ0,hΦode⟩ :=
      exists_smooth_local_manifold_flow hv (completeFlow hc s a)
    refine ⟨r,hr,?_⟩
    intro t ht
    exact completeFlow_smooth_step hc hv hr hU hΦ hΦ0 hΦode hs hUa
      (by simpa only [Metric.mem_ball,Real.dist_eq,abs_lt,mem_Ioo] using ht)
  have hcompl : IsOpen Tᶜ := by
    apply Metric.isOpen_iff.mpr
    intro t ht
    obtain ⟨r,hr,U,hU,hUa,Φ,hΦ,hΦ0,hΦode⟩ :=
      exists_smooth_local_manifold_flow hv (completeFlow hc t a)
    have hnear := (completeFlow_curve hc a).continuous.continuousAt.preimage_mem_nhds
      (hU.mem_nhds hUa)
    obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hnear
    refine ⟨min r δ,lt_min hr hδ,?_⟩
    intro s hs hsm
    have hsr : dist s t < r := lt_of_lt_of_le hs (min_le_left _ _)
    have hsδ : dist s t < δ := lt_of_lt_of_le hs (min_le_right _ _)
    apply ht
    exact completeFlow_smooth_step hc hv hr hU hΦ hΦ0 hΦode hsm (hδU hsδ)
      (by simpa only [Real.dist_eq,abs_sub_comm,abs_lt,mem_Ioo] using hsr)
  have hTuniv : T = univ := (IsClopen.eq_univ ⟨isOpen_compl_iff.mp hcompl,hopen⟩ ⟨0,hT0⟩)
  change t ∈ T
  rw [hTuniv]
  exact mem_univ t

lemma contMDiff_completeFlow :
    ContMDiff (𝓘(ℝ,ℝ).prod I) I ∞ (fun z : ℝ × M => completeFlow hc z.1 z.2) := by
  intro z
  obtain ⟨r,hr,U,hU,hUa,Φ,hΦ,hΦ0,hΦode⟩ :=
    exists_smooth_local_manifold_flow hv (completeFlow hc z.1 z.2)
  have hs := (contMDiff_completeFlow_time_slice hc hv z.1) z.2
  have hpair : ContMDiffAt (𝓘(ℝ,ℝ).prod I) (𝓘(ℝ,ℝ).prod I) ∞
      (fun w : ℝ × M => (w.1-z.1,completeFlow hc z.1 w.2)) z :=
    (contMDiffAt_fst.sub contMDiffAt_const).prodMk (hs.comp z contMDiffAt_snd)
  have hsm := (hΦ.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds
    (show (z.1-z.1,completeFlow hc z.1 z.2) ∈ Ioo (-r) r ×ˢ U from
      ⟨by simp only [sub_self,mem_Ioo]; exact ⟨neg_lt_zero.mpr hr,hr⟩,hUa⟩))).comp z hpair
  apply hsm.congr_of_eventuallyEq
  have hnear := hpair.continuousAt.preimage_mem_nhds
    ((isOpen_Ioo.prod hU).mem_nhds
      (show (z.1-z.1,completeFlow hc z.1 z.2) ∈ Ioo (-r) r ×ˢ U from
        ⟨by simp only [sub_self,mem_Ioo]; exact ⟨neg_lt_zero.mpr hr,hr⟩,hUa⟩))
  filter_upwards [hnear] with w hw
  change completeFlow hc w.1 w.2 = Φ (w.1-z.1,completeFlow hc z.1 w.2)
  rw [← completeFlow_eq_local hc hv hr hΦ0 hΦode hw.2 hw.1,
    ← completeFlow_add hc hv,sub_add_cancel]

end WeakMTWTransport

end

end OAI
