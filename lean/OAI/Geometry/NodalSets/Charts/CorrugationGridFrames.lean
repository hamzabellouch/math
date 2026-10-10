import OAI.Geometry.NodalSets.Elliptic.CorrugationCubePartition
import OAI.Geometry.NodalSets.Elliptic.CorrugationOldData

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

theorem exists_corrugation_grid_frames (o : Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (hp : ∀ y ∈ Icc o (fun i ↦ o i+L), ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ Icc o (fun i ↦ o i+L), ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ Icc o (fun i ↦ o i+L), metricGradient g S y ≠ 0 ∧
      ∃ q : Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q) :
    ∃ e : (Fin 4 → Fin n) → Coord ≃L[ℝ] Coord,
      ∀ i, let y := corrugationCubeCenter o L n i
      e i (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y ∧
      (∀ a b, g y (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0) ∧
      (∀ v, g y v v = 1 → g y (metricGradient g S y) v = 0 →
        sourceHessian g S y v v ≤ sourceHessian g S y (e i (Pi.single 1 1)) (e i (Pi.single 1 1))) ∧
      0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
        (g y (metricGradient g S y) (metricGradient g S y)+4)*
          sourceHessian g S y (e i (Pi.single 1 1)) (e i (Pi.single 1 1)) := by
  have hex : ∀ i : Fin 4 → Fin n, ∃ e : Coord ≃L[ℝ] Coord,
      let y := corrugationCubeCenter o L n i
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y ∧
      (∀ a b, g y (e (Pi.single a 1)) (e (Pi.single b 1)) = if a=b then 1 else 0) ∧
      (∀ v, g y v v = 1 → g y (metricGradient g S y) v = 0 →
        sourceHessian g S y v v ≤ sourceHessian g S y (e (Pi.single 1 1)) (e (Pi.single 1 1))) ∧
      0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
        (g y (metricGradient g S y) (metricGradient g S y)+4)*
          sourceHessian g S y (e (Pi.single 1 1)) (e (Pi.single 1 1)) := by
    intro i
    let y := corrugationCubeCenter o L n i
    have hy := corrugationCubeCenter_mem o hL hn i
    obtain ⟨hp0,q0,hq0,hpq0,hstr⟩ := hadm y hy
    obtain ⟨q,e,hq,hpq,hmax,he0,he1,he,_⟩ := exists_corrugation_frozen_frame
      (g y) (sourceHessian g S y) (hp y hy) (hsym y hy) (metricGradient g S y) q0 hp0 hq0 hpq0
    refine ⟨e,he0,he,?_,?_⟩
    · rw [he1]
      exact hmax
    · rw [he1]
      have hmax0 := hmax q0 hq0 hpq0
      have hgpos := hp y hy (metricGradient g S y) hp0
      have hh := mul_le_mul_of_nonneg_left hmax0 (by positivity : 0 ≤ g y (metricGradient g S y) (metricGradient g S y)+4)
      linarith
  choose e he using hex
  exact ⟨e,he⟩

end
end Yau.Geometry

end OAI
