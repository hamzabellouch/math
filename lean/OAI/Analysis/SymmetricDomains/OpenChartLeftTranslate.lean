import Mathlib
import OAI.Analysis.SymmetricDomains.FirstJetConstMul2

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

namespace Biholomorph
open Set Filter Topology Metric
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U)
include hU hc hbd Γ hhol

theorem exists_actual_aut_chart_COne_translations :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
    ∃ e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
      (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)) ∧
      1∈e.source ∧
      (∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc hbd Γ hhol p X) ∧
      ∀ (g h : Biholomorph U U) y, y∈e.target →
        ContDiffAt ℝ 1 (fun t => e (g*e.symm t*h)) y := by
  let R : Type := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  obtain ⟨P,e,he,he1,hP,hreg⟩ := exists_actual_aut_firstJet_COne_neighborhood hU hc hbd Γ hhol p
  refine ⟨P,e,he,he1,hP,?_⟩
  intro g h y hy
  have hr := firstJet_mul_const_contDiffAt hU p h e.symm y (hreg (h.toHomeomorph p) y hy)
  have hl := firstJet_const_mul_contDiffAt hU p g (fun t => e.symm t*h) y hr
  have hPdiff := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1)
      (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R) P).contDiffAt.comp y hl
  simpa only [Function.comp_def,he,mul_assoc] using hPdiff
end Biholomorph

open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem openChart_leftTranslate_det_ne_zero
    (e : OpenPartialHomeomorph G E)
    (hC : ∀ (g : G) y, y∈e.target →
      ContDiffAt ℝ 1 (fun t => e (g*e.symm t)) y)
    (g : G) (y : E) (hy : y∈e.target) (hg : g*e.symm y∈e.source) :
    LinearMap.det (M := E) (fderiv ℝ (fun t => e (g*e.symm t)) y).toLinearMap ≠ 0 := by
  let f : E → E := fun t => e (g*e.symm t)
  let q : E → E := fun t => e (g⁻¹*e.symm t)
  have hf : DifferentiableAt ℝ f y := (hC g y hy).differentiableAt (by simp)
  have hfy : f y∈e.target := e.map_source hg
  have hq : DifferentiableAt ℝ q (f y) := (hC g⁻¹ (f y) hfy).differentiableAt (by simp)
  have hc : ContinuousAt (fun t => g*e.symm t) y :=
    continuousAt_const.mul (e.symm.continuousAt hy)
  have hs : ∀ᶠ t in 𝓝 y, g*e.symm t∈e.source :=
    hc.preimage_mem_nhds (e.open_source.mem_nhds hg)
  have ht : ∀ᶠ t in 𝓝 y, t∈e.target := e.open_target.mem_nhds hy
  have heq : (q ∘ f) =ᶠ[𝓝 y] id := by
    filter_upwards [hs,ht] with t hgt ht
    dsimp only [q,f,Function.comp_apply,id_eq]
    rw [e.left_inv hgt,inv_mul_cancel_left,e.right_inv ht]
  have hd := (hq.hasFDerivAt.comp y hf.hasFDerivAt).congr_of_eventuallyEq heq.symm
  have hcomp : (fderiv ℝ q (f y)).comp (fderiv ℝ f y)=ContinuousLinearMap.id ℝ E :=
    hd.unique (hasFDerivAt_id y)
  have hinj : Function.Injective (fderiv ℝ f y) := by
    intro u v huv
    have h := congrArg (fderiv ℝ q (f y)) huv
    simpa only [←ContinuousLinearMap.comp_apply,hcomp,ContinuousLinearMap.id_apply] using h
  intro hz
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hinj)
end Release061

end

end OAI
