import Mathlib
import OAI.Analysis.Conductivity.Variational.NormalStretch

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped ENNReal Matrix.Norms.Elementwise

lemma localPullback_tsupport_inside
    {E V : Type*} [TopologicalSpace E] [T2Space E] [Zero V]
    (X : OpenPartialHomeomorph E E) (f : E → V) (hf : HasCompactSupport f)
    {U : Set E} (hU : U ⊆ X.source) (hfs : tsupport f ⊆ X '' U) :
    tsupport (localPullback X f) ⊆ U := by
  have ht : tsupport f ⊆ X.target := hfs.trans (by
    rintro y ⟨x, hx, rfl⟩; exact X.map_source (hU hx))
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (localPullback_tsupport X f hf ht).2.1 hx
  obtain ⟨z, hz, rfl⟩ := hfs hy
  simpa only [X.left_inv (hU hz)] using hz

lemma pushed_exception_measure_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (Y : E ≃ E) (hY : Differentiable ℝ Y) {U : Set E} (hU : MeasurableSet U)
    (hYU : Y '' U = U) (z : E → ℝ) (hz : Continuous z) (a b : ℝ)
    {C : ℝ} (hC : ∀ x, |(fderiv ℝ Y x).det| ≤ C) :
    μ {x | x ∈ U ∧ z (Y.symm x) ≠ a ∧ z (Y.symm x) ≠ b} ≤
      ENNReal.ofReal C * μ {x | x ∈ U ∧ z x ≠ a ∧ z x ≠ b} := by
  let S := {x | x ∈ U ∧ z x ≠ a ∧ z x ≠ b}
  have hS : MeasurableSet S := hU.inter
    (((isOpen_ne.preimage hz).measurableSet).inter ((isOpen_ne.preimage hz).measurableSet))
  have he : Y '' S = {x | x ∈ U ∧ z (Y.symm x) ≠ a ∧ z (Y.symm x) ≠ b} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hYU ▸ mem_image_of_mem Y hy.1, by simpa only [Y.symm_apply_apply] using hy.2⟩
    · intro hx
      have hxU : Y.symm x ∈ U := by
        obtain ⟨y, hy, he⟩ := (show x ∈ Y '' U from hYU.symm ▸ hx.1)
        simpa only [← he, Y.symm_apply_apply] using hy
      exact ⟨Y.symm x, ⟨hxU, hx.2⟩, Y.apply_symm_apply x⟩
  rw [← he]
  exact measure_image_le_det μ hS (fun x _ => hY x) Y.injective.injOn (fun x _ => hC x)

end ScalarConductivity

end

end OAI
