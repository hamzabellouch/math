import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

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
namespace Release061
open Set

@[instance_reducible] def conjugateMulAction {G X Y : Type*} [Monoid G] [MulAction G X]
    (e : X ≃ Y) : MulAction G Y where
  smul g y := e (g • e.symm y)
  one_smul y := by
    change e ((1 : G) • e.symm y) = y
    simp
  mul_smul g h y := by
    change e ((g*h) • e.symm y) = e (g • e.symm (e (h • e.symm y)))
    simp [mul_smul]

lemma conjugateMulAction_smul {G X Y : Type*} [Monoid G] [MulAction G X]
    (e : X ≃ Y) (g : G) (x : X) :
    let _ : MulAction G Y := conjugateMulAction e
    g • e x = e (g • x) := by
  change e (g • e.symm (e x)) = e (g • x)
  rw [e.symm_apply_apply]

theorem conjugateMulAction_proper {G X Y : Type*} [Group G]
    [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y]
    [MulAction G X] [ProperSMul G X] (e : X ≃ₜ Y) :
    let _ : MulAction G Y := conjugateMulAction e.toEquiv
    ProperSMul G Y := by
  let _ : MulAction G Y := conjugateMulAction e.toEquiv
  constructor
  change IsProperMap (fun gx : G × Y => (e (gx.1 • e.symm gx.2),gx.2))
  have H := ((e.prodCongr e).isProperMap.comp
    (ProperSMul.isProperMap_smul_pair (G := G) (X := X))).comp
    ((Homeomorph.refl G).prodCongr e.symm).isProperMap
  change IsProperMap (fun gx : G × Y => (e (gx.1 • e.symm gx.2),e (e.symm gx.2))) at H
  simpa only [e.apply_symm_apply] using H

theorem conjugateMulAction_compact_quotient {G X Y : Type*} [Group G]
    [TopologicalSpace X] [TopologicalSpace Y] [MulAction G X]
    [CompactSpace (Quotient (MulAction.orbitRel G X))] (e : X ≃ₜ Y) :
    let _ : MulAction G Y := conjugateMulAction e.toEquiv
    CompactSpace (Quotient (MulAction.orbitRel G Y)) := by
  let _ : MulAction G Y := conjugateMulAction e.toEquiv
  have hr : ∀ x x' : X, MulAction.orbitRel G X x x' →
      MulAction.orbitRel G Y (e x) (e x') := by
    intro x x' h
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨g,?_⟩
    change e (g • e.symm (e x')) = e x
    simpa only [e.symm_apply_apply] using congrArg e hg
  let f : Quotient (MulAction.orbitRel G X) → Quotient (MulAction.orbitRel G Y) :=
    Quotient.map' e hr
  have hf : Continuous f := e.continuous.quotient_map' hr
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨y,rfl⟩ := Quotient.mk_surjective y
    refine ⟨Quotient.mk _ (e.symm y),?_⟩
    simp [f]
  exact ⟨by simpa only [Set.image_univ,hs.range_eq] using isCompact_univ.image hf⟩

end Release061

end

end OAI
