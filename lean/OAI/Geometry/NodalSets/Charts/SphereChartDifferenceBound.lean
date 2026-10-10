import OAI.Geometry.NodalSets.Charts.SphereChartCutoffApproximation
import OAI.Geometry.NodalSets.Elliptic.RealL2DifferenceLimit
import OAI.Geometry.NodalSets.Elliptic.RealSmoothDifferenceBound

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section
local instance sphereChartDifferenceMeasurable : MeasurableSpace Base := borel Base
local instance sphereChartDifferenceBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_chart_cutoff_difference_norm_bound (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (i : Fin 4) (h : ℝ) :
    ‖Yau.realL2DifferenceMap i h (sphereCutoffValueMap d p eta he hs z)‖^2 ≤
      ‖sphereCutoffDerivativeMap d p eta he hs i z‖^2 := by
  obtain ⟨u,_,ha⟩ := sphere_chart_cutoff_strong_approximation d z
  have hc : HasCompactSupport eta :=
    (realFinCube_isCompact 4).of_isClosed_subset (isClosed_tsupport eta) hs
  apply Yau.real_difference_norm_bound_limit i h _ _ _ _ (ha p eta he hs).1 ((ha p eta he hs).2 i)
  intro k
  let v : Yau.Jets.Coord → ℝ := fun x ↦ eta x*(SphereEnergySmooth.toSmooth d (u k) : Base → ℝ)
    (sphereChartCoordMap p x)
  have hv : ContDiff ℝ ∞ v := he.mul
    (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d (u k)).property p)
  have hb := (Yau.real_smooth_difference_bound v hv hc.mul_right i h).2
  have hvrep := sphereCutoffValueMap_smooth_ae d p eta he hs (u k)
  have hgrep := sphereCutoffDerivativeMap_smooth_ae d p eta he hs i (u k)
  rw [Yau.real_L2_norm_sq_rep _ _ (Yau.realL2DifferenceMap_ae i h _ v hvrep),
    Yau.real_L2_norm_sq_rep _ _ hgrep]
  exact hb

theorem sphere_chart_cutoff_difference_bound (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (i : Fin 4) (h : ℝ) :
    let v := fun x ↦ eta x*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    let G := fun x ↦ eta x*(sphereChartDerivativeMap d p i z) x +
      Yau.coordPartial eta x i*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    MemLp (Yau.realDifferenceQuotient i h v) 2 volume ∧
      (∫ x, (Yau.realDifferenceQuotient i h v x)^2) ≤ ∫ x, (G x)^2 := by
  dsimp only
  have hv := sphereCutoffValueMap_ae d p eta he hs z
  have hg := sphereCutoffDerivativeMap_ae d p eta he hs i z
  have hb := sphere_chart_cutoff_difference_norm_bound d p z eta he hs i h
  rw [Yau.real_L2_norm_sq_rep _ _ (Yau.realL2DifferenceMap_ae i h _ _ hv),
    Yau.real_L2_norm_sq_rep _ _ hg] at hb
  exact ⟨Yau.realDifferenceQuotient_memLp i h _ (sphere_chart_cutoff_weak d p z eta he hs).1,hb⟩

end
end Yau.Target

end OAI
