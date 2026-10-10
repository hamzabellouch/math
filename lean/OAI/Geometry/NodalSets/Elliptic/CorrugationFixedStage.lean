import OAI.Geometry.NodalSets.Elliptic.CorrugationAdmissibleStage
import OAI.Geometry.NodalSets.Elliptic.CorrugationFixedCutoff

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

theorem exists_small_fixed_admissible_corrugation (o : Coord) {L : ℝ} (hL : 0 < L)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    {U : Set Coord} (hU : IsOpen U) (hDU : Icc o (fun i ↦ o i+L) ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ Icc o (fun i ↦ o i+L), ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ Icc o (fun i ↦ o i+L), metricGradient g S y ≠ 0 ∧
      ∃ q : Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ∃ e : (Fin 4 → Fin (corrugationSubdivision k)) → Coord ≃L[ℝ] Coord,
      let w := corrugationEnvelopePerturbation o L k g S corrugationFixedCutoff corrugationFixedAmplitude e
      ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      tsupport w ⊆ interior (Icc o (fun i ↦ o i+L)) ∧ (∀ x, |w x| < ε) ∧
      (∀ i, let y := corrugationCubeCenter o L (corrugationSubdivision k) i
        e i (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y ∧
        (∀ a b, g y (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0) ∧
        (∀ v, g y v v = 1 → g y (metricGradient g S y) v = 0 →
          sourceHessian g S y v v ≤ sourceHessian g S y (e i (Pi.single 1 1)) (e i (Pi.single 1 1)))) ∧
      ∃ V : Set Coord, IsOpen V ∧ Icc o (fun i ↦ o i+L) ⊆ V ∧ V ⊆ U ∧
        ∀ x ∈ V, metricGradient g (S+w) x ≠ 0 ∧
          ∃ t : Coord, g x t t = 1 ∧ g x (metricGradient g (S+w) x) t = 0 ∧
            0 < sourceHessian g (S+w) x (metricGradient g (S+w) x) (metricGradient g (S+w) x) +
              (g x (metricGradient g (S+w) x) (metricGradient g (S+w) x)+4)*sourceHessian g (S+w) x t t := by
  obtain ⟨C,hC,hχ,hc,hsupp,hrange,_,hder⟩ := corrugationFixedCutoff_spec
  exact exists_small_admissible_corrugation o hL g S corrugationFixedCutoff hU hDU hg hS hp hsym hadm
    hχ hsupp (fun z ↦ (hrange z).1) (fun z ↦ (hrange z).2) hC hder hε

end
end Yau.Geometry

end OAI
