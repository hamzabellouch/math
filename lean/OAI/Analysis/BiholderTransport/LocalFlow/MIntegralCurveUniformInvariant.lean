import Mathlib
import OAI.Analysis.BiholderTransport.LocalFlow.LocalDomainFlow

namespace OAI

noncomputable section

namespace WeakMTWTransport

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

section
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [T2Space M]

lemma exists_isMIntegralCurve_of_uniform_invariant_set [BoundarylessManifold I M]
    {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {ε : ℝ} (hε : 0 < ε) {K : Set M}
    (h : ∀ x ∈ K, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε))
    (hinv : ∀ (a : ℝ) (γ : ℝ → M), γ 0 ∈ K →
      IsMIntegralCurveOn γ v (Ioo (-a) a) → MapsTo γ (Ioo (-a) a) K)
    (x : M) (hx : x ∈ K) : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  let s := { a | ∃ γ, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-a) a) }
  suffices hbdd : ¬BddAbove s by
    rw [not_bddAbove_iff] at hbdd
    rw [exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hv]
    intro a
    obtain ⟨y, ⟨γ, hγ1, hγ2⟩, hlt⟩ := hbdd a
    exact ⟨γ, hγ1, hγ2.mono <| Ioo_subset_Ioo (neg_le_neg hlt.le) hlt.le⟩
  intro hbdd
  set asup := sSup s with hasup

  obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup (⟨ε, h x hx⟩ : Set.Nonempty s) (ε := - (ε / 2))
    (by rw [neg_lt, neg_zero]; exact half_pos hε)
  rw [mem_ofPred] at ha
  rw [← hasup, ← sub_eq_add_neg] at hlt

  obtain ⟨γ, h0, hγ⟩ := ha
  have hεle : ε ≤ asup := le_csSup hbdd (h x hx)

  obtain ⟨γ1_aux, h1_aux, hγ1⟩ := h (γ (-(asup - ε / 2)))
    (hinv a γ (h0 ▸ hx) hγ ⟨by linarith, by linarith⟩)
  rw [← isMIntegralCurveOn_comp_add (dt := asup - ε / 2)] at hγ1
  set γ1 := γ1_aux ∘ (· + (asup - ε / 2)) with γ1_def
  have heq1 : γ1 (-(asup - ε / 2)) = γ (-(asup - ε / 2)) := by simp [γ1_def, h1_aux]

  obtain ⟨γ2_aux, h2_aux, hγ2⟩ := h (γ (asup - ε / 2))
    (hinv a γ (h0 ▸ hx) hγ ⟨by linarith, hlt⟩)
  rw [← isMIntegralCurveOn_comp_sub (dt := asup - ε / 2)] at hγ2
  set γ2 := γ2_aux ∘ (· - (asup - ε / 2)) with γ2_def
  have heq2 : γ2 (asup - ε / 2) = γ (asup - ε / 2) := by simp [γ2_def, h2_aux]

  simp_rw [Set.mem_Ioo, ← sub_lt_iff_lt_add, ← lt_sub_iff_add_lt, ← Set.mem_Ioo] at hγ1
  simp_rw [Set.mem_Ioo, lt_sub_iff_add_lt, sub_lt_iff_lt_add, ← Set.mem_Ioo] at hγ2

  set γ_ext : ℝ → M := piecewise (Ioo (-(asup + ε / 2)) a)
    (piecewise (Ioo (-a) a) γ γ1) γ2 with γ_ext_def
  have heq_ext : γ_ext 0 = x := by
    rw [γ_ext_def, piecewise, ite_eq_left ⟨by linarith, by linarith⟩, piecewise,
      ite_eq_left ⟨by linarith, by linarith⟩, h0]

  suffices hext : IsMIntegralCurveOn γ_ext v (Ioo (-(asup + ε / 2)) (asup + ε / 2)) from
    (not_lt.mpr <| le_csSup hbdd ⟨γ_ext, heq_ext, hext⟩) <| lt_add_of_pos_right asup (half_pos hε)
  apply (isMIntegralCurveOn_piecewise (t₀ := asup - ε / 2) hv _ hγ2
      ⟨⟨by linarith, hlt⟩, ⟨by linarith, by linarith⟩⟩
      (by rw [piecewise, ite_eq_left ⟨by linarith, hlt⟩, ← heq2])).mono
    (Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith))
  exact (isMIntegralCurveOn_piecewise (t₀ := -(asup - ε / 2)) hv hγ hγ1
      ⟨⟨neg_lt_neg hlt, by linarith⟩, ⟨by linarith, by linarith⟩⟩ heq1.symm).mono
    (union_comm _ _ ▸ Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl)

end
open Manifold Bundle
open scoped Manifold Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

lemma hasMFDerivAt_of_chart_ode {v : (x : M) → TangentSpace I x}
    (a : M) {f : ℝ → E} {t : ℝ}
    (ht : f t ∈ (extChartAt I a).target)
    (hf : HasDerivAt f
      (tangentCoordChange I ((extChartAt I a).symm (f t)) a
        ((extChartAt I a).symm (f t)) (v ((extChartAt I a).symm (f t)))) t) :
    HasMFDerivAt 𝓘(ℝ,ℝ) I ((extChartAt I a).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((extChartAt I a).symm (f t)))) := by
  let xₜ := (extChartAt I a).symm (f t)
  have hft1 := (extChartAt I a).map_target ht
  have hft2 := mem_extChartAt_source (I := I) xₜ
  let w : E := v xₜ
  change HasDerivAt f (tangentCoordChange I xₜ a xₜ w) t at hf
  have hder : HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I a).symm) ∘ f)
      w t := by
    have he : tangentCoordChange I a xₜ xₜ (tangentCoordChange I xₜ a xₜ w) = w := by
      rw [tangentCoordChange_comp ⟨⟨hft2,hft1⟩,hft2⟩,tangentCoordChange_self hft2]
    rw [← he]
    apply HasFDerivAt.comp_hasDerivAt _ _ hf
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _
      (by simp only [ModelWithCorners.range_eq_univ,univ_mem])
    rw [← (extChartAt I a).right_inv ht]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1,hft2⟩
  refine ⟨(continuousAt_extChartAt_symm'' ht).comp hf.continuousAt,?_⟩
  rw [writtenInExtChartAt,extChartAt_model_space_eq_id,ModelWithCorners.range_eq_univ]
  change HasFDerivWithinAt ((extChartAt I xₜ ∘ (extChartAt I a).symm) ∘ f)
    ((1 : ℝ →L[ℝ] ℝ).smulRight w) univ t
  rw [hasFDerivWithinAt_univ]
  convert! hder.hasFDerivAt using 1

omit [I.Boundaryless] in
lemma contDiffOn_coordinate_vectorField {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞
      (fun x => (⟨x,v x⟩ : TangentBundle I M))) (a : M) :
    ContDiffOn ℝ ∞ (fun y => tangentCoordChange I ((extChartAt I a).symm y) a
      ((extChartAt I a).symm y) (v ((extChartAt I a).symm y))) (extChartAt I a).target := by
  let e := trivializationAt E (fun x : M => TangentSpace I x) a
  have hc : ContMDiffOn I 𝓘(ℝ,E) ∞ (fun x => (e ⟨x,v x⟩).2) e.baseSet := by
    intro x hx
    exact ((e.contMDiffAt_section_iff hx).mp (hv x)).contMDiffWithinAt
  have hmaps : MapsTo (extChartAt I a).symm (extChartAt I a).target e.baseSet := by
    intro y hy
    change (extChartAt I a).symm y ∈ (chartAt H a).source
    simpa only [extChartAt_source] using (extChartAt I a).map_target hy
  exact contMDiffOn_iff_contDiffOn.mp (hc.comp (contMDiffOn_extChartAt_symm a) hmaps)

lemma exists_uniform_local_manifold_curves [CompleteSpace E] [HasContDiffBump E]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞
      (fun x => (⟨x,v x⟩ : TangentBundle I M))) (a : M) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set M, U ∈ 𝓝 a ∧
      ∀ x ∈ U, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  let c := extChartAt I a
  obtain ⟨r,hr,_,Φ,_,hΦ0,hΦder⟩ := exists_smooth_local_flow_on
    (isOpen_extChartAt_target a) (contDiffOn_coordinate_vectorField hv a)
      (c.map_source (mem_extChartAt_source a))
  let U := c.source ∩ c ⁻¹' Metric.ball (c a) r
  have hUa : U ∈ 𝓝 a := inter_mem (extChartAt_source_mem_nhds a)
    ((continuousAt_extChartAt (I := I) (x := a)).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  refine ⟨r,hr,U,hUa,?_⟩
  intro x hx
  refine ⟨c.symm ∘ (fun t => Φ (t,c x)),?_,?_⟩
  · simp only [Function.comp_apply,hΦ0 _ hx.2,c.left_inv hx.1]
  · intro t ht
    exact (hasMFDerivAt_of_chart_ode a (hΦder t ht (c x) hx.2).1
      (hΦder t ht (c x) hx.2).2).hasMFDerivWithinAt

end WeakMTWTransport

end

end OAI
