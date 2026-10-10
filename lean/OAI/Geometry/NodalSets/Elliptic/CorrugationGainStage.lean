import OAI.Geometry.NodalSets.Elliptic.CorrugationFixedStage
import OAI.Geometry.NodalSets.Elliptic.CorrugationGridGain

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric MeasureTheory
open scoped ContDiff Topology
noncomputable section

abbrev sourceDirectionalAdmissibleOn
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ) (D : Set Coord) : Prop :=
  ∀ x ∈ D, metricGradient g S x ≠ 0 ∧
    ∃ t : Coord, g x t t = 1 ∧ g x (metricGradient g S x) t = 0 ∧
      0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x) +
        (g x (metricGradient g S x) (metricGradient g S x)+4)*sourceHessian g S x t t

theorem exists_small_corrugation_gain_stage {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (o : Coord) (L : ℝ), 0 < L →
      ∀ (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (U : Set Coord),
      IsOpen U → Icc o (fun j ↦ o j+L) ⊆ U → ContDiffOn ℝ ∞ g U →
      (∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), ∀ u v, g y u v = g y v u) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v) →
      ∀ S : Coord → ℝ, ContDiffOn ℝ ∞ S U →
      sourceDirectionalAdmissibleOn g S (Icc o (fun j ↦ o j+L)) →
      ∀ ε : ℝ, 0 < ε → ∃ w : Coord → ℝ,
      ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      tsupport w ⊆ interior (Icc o (fun j ↦ o j+L)) ∧ (∀ x, |w x| < ε) ∧
      sourceDirectionalAdmissibleOn g (S+w) (Icc o (fun j ↦ o j+L)) ∧
      (1+γ)*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x) ≤
        ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g (S+w) x := by
  obtain ⟨γ,hγ,hgain⟩ := corrugation_grid_integrated_gain hc hM
  refine ⟨γ,hγ,?_⟩
  intro o L hL g U hU hDU hg hp hsym hcmp S hS hadm ε hε
  have hsmall := exists_small_fixed_admissible_corrugation o hL g S hU hDU hg hS hp hsym hadm hε
  have hgain' := hgain o L hL g S U hU hDU hg hS hp (fun y hy ↦ (hadm y hy).1) hcmp
  obtain ⟨k,hk,hgaink⟩ := (hsmall.and hgain').exists
  obtain ⟨e,hsmooth,hcompact,hsupp,hsmall,hframe,V,hV,hDV,hVU,hadmnew⟩ := hk
  refine ⟨corrugationEnvelopePerturbation o L k g S corrugationFixedCutoff corrugationFixedAmplitude e,
    hsmooth,hcompact,hsupp,hsmall,fun x hx ↦ hadmnew x (hDV hx),?_⟩
  exact hgaink e (fun i ↦ ⟨(hframe i).1,(hframe i).2.1⟩)

end
end Yau.Geometry

end OAI
