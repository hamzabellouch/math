import OAI.Geometry.NodalSets.Elliptic.CorrugationCellGain
import OAI.Geometry.NodalSets.Elliptic.CorrugationClosedCubeLocality
import OAI.Geometry.NodalSets.Elliptic.CorrugationCubeIntegral
import OAI.Geometry.NodalSets.Elliptic.CorrugationGridProperties

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem corrugation_grid_integrated_gain {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (o : Coord) (L : ℝ), 0 < L →
      ∀ (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
      (U : Set Coord), IsOpen U → Icc o (fun j ↦ o j+L) ⊆ U →
      ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ S U →
      (∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), metricGradient g S y ≠ 0) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v) →
      ∀ᶠ k : ℕ in atTop,
      ∀ e : (Fin 4 → Fin (corrugationSubdivision k)) → Coord ≃L[ℝ] Coord,
      (∀ i, let y := corrugationCubeCenter o L (corrugationSubdivision k) i
        e i (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y ∧
        (∀ a b, g y (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0)) →
      (1+γ)*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x) ≤
        ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g
          (S+corrugationEnvelopePerturbation o L k g S corrugationFixedCutoff corrugationFixedAmplitude e) x := by
  obtain ⟨γ,hγ,hcell⟩ := corrugation_cell_integrated_gain hc hM
  refine ⟨γ,hγ,?_⟩
  intro o L hL g S U hU hDU hg hS hp hn hcmp
  have hev := hcell g S (Icc o (fun j ↦ o j+L)) U isCompact_Icc
    (convex_Icc o (fun j ↦ o j+L)) hU hDU hg hS hp hn hcmp L hL
  filter_upwards [hev] with k hk
  intro e he
  let n := corrugationSubdivision k
  let y := corrugationCubeCenter o L n
  let W := corrugationEnvelopePerturbation o L k g S corrugationFixedCutoff corrugationFixedAmplitude e
  obtain ⟨_,_,hχ,_,hsupp,_,_,_⟩ := corrugationFixedCutoff_spec
  have hW : ContDiff ℝ ∞ W := corrugationEnvelopePerturbation_smooth o L k g S _ _ e hχ
  have ho : IntegrableOn (corrugationOldSlope g S) (Icc o (fun j ↦ o j+L)) :=
    ((corrugationOldSlope_continuousOn g S hU hg hS hp).mono hDU).integrableOn_Icc
  have hf : IntegrableOn (corrugationOldSlope g (S+W)) (Icc o (fun j ↦ o j+L)) :=
    ((corrugationOldSlope_continuousOn g (S+W) hU hg (hS.add hW.contDiffOn) hp).mono hDU).integrableOn_Icc
  rw [corrugation_cube_integral_sum o hL (corrugationSubdivision_positive k) _ ho,
    corrugation_cube_integral_sum o hL (corrugationSubdivision_positive k) _ hf,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi := hk (y i) (corrugationCubeCenter_mem o hL (corrugationSubdivision_positive k) i)
    (corrugationCube_closed_inside o hL (corrugationSubdivision_positive k) i) (e i) (he i).1 (he i).2
  apply hi.trans_eq
  apply setIntegral_congr_fun measurableSet_closedBall
  intro x hx
  have heq := corrugationGridSum_closed_cube_eventually o hL (corrugationSubdivision_positive k)
    corrugationFixedCutoff hsupp corrugationFixedAmplitude (corrugationFrequency k)
    (fun j ↦ corrugationOldSlope g S (y j)) e i x hx
  have heq' := Filter.EventuallyEq.add (Filter.EventuallyEq.rfl (f := S)) heq
  exact (congrArg (fun p : Coord ↦ Real.sqrt (g x p p))
    (congrArg (fun d : Coord →L[ℝ] ℝ ↦ ContinuousLinearMap.inverse (g x) d) heq'.fderiv_eq)).symm

end
end Yau.Geometry

end OAI
