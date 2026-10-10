import OAI.Geometry.NodalSets.Charts.SphereChartCutoffApproximation
import OAI.Geometry.NodalSets.Elliptic.RealGlobalL2Multiplier

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section
local instance sphereDifferenceTestMeasurable : MeasurableSpace Base := borel Base
local instance sphereDifferenceTestBorel : BorelSpace Base := ⟨rfl⟩

def sphereDifferenceTestMap (d : SphereEnergyData) (p : Base)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) : SphereEnergyHilbert d →L[ℝ] Yau.RealEuclideanL2 4 :=
  (Yau.realGlobalCompactMap (realFinCube_isCompact 4) theta ht.continuous hts).comp
    ((Yau.realL2DifferenceMap i h).comp (sphereCutoffValueMap d p eta he hes))

def sphereDifferenceTestDerivativeMap (d : SphereEnergyData) (p : Base)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (j : Fin 4) : SphereEnergyHilbert d →L[ℝ] Yau.RealEuclideanL2 4 :=
  (Yau.realGlobalCompactMap (realFinCube_isCompact 4) theta ht.continuous hts).comp
    ((Yau.realL2DifferenceMap i h).comp (sphereCutoffDerivativeMap d p eta he hes j)) +
  (Yau.realGlobalCompactMap (realFinCube_isCompact 4) (fun x ↦ Yau.coordPartial theta x j)
    (Yau.real_coordPartial_smooth theta ht j).continuous
    ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans hts)).comp
    ((Yau.realL2DifferenceMap i h).comp (sphereCutoffValueMap d p eta he hes))

theorem sphereDifferenceTestMap_ae (d : SphereEnergyData) (p : Base)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (z : SphereEnergyHilbert d) :
    (sphereDifferenceTestMap d p eta theta he ht hes hts i h z : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] (fun x ↦ theta x*Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x) :=
  Yau.realGlobalCompactMap_ae (realFinCube_isCompact 4) theta ht.continuous hts _ _
    (Yau.realL2DifferenceMap_ae i h _ _ (sphereCutoffValueMap_ae d p eta he hes z))

theorem sphereDifferenceTestDerivativeMap_ae (d : SphereEnergyData) (p : Base)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (j : Fin 4) (z : SphereEnergyHilbert d) :
    (sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j z : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] (fun x ↦ theta x*Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(sphereChartDerivativeMap d p j z) y+
          Yau.coordPartial eta y j*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x +
        Yau.coordPartial theta x j*Yau.realDifferenceQuotient i h
          (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x) := by
  exact (Lp.coeFn_add _ _).trans
    ((Yau.realGlobalCompactMap_ae (realFinCube_isCompact 4) theta ht.continuous hts _ _
      (Yau.realL2DifferenceMap_ae i h _ _ (sphereCutoffDerivativeMap_ae d p eta he hes j z))).add
    (Yau.realGlobalCompactMap_ae (realFinCube_isCompact 4) _
      (Yau.real_coordPartial_smooth theta ht j).continuous
      ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans hts) _ _
      (Yau.realL2DifferenceMap_ae i h _ _ (sphereCutoffValueMap_ae d p eta he hes z))))

theorem sphereDifferenceTestMap_smooth_ae (d : SphereEnergyData) (p : Base)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (u : SphereEnergySmooth d) :
    (sphereDifferenceTestMap d p eta theta he ht hes hts i h (sphereEnergyToCompletion d u) : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] (fun x ↦ theta x*Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p y)) x) :=
  Yau.realGlobalCompactMap_ae (realFinCube_isCompact 4) theta ht.continuous hts _ _
    (Yau.realL2DifferenceMap_ae i h _ _ (sphereCutoffValueMap_smooth_ae d p eta he hes u))

theorem sphereDifferenceTestDerivativeMap_smooth_ae (d : SphereEnergyData) (p : Base)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (j : Fin 4) (u : SphereEnergySmooth d) :
    (sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j (sphereEnergyToCompletion d u) : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] (fun x ↦ Yau.coordPartial (fun y ↦ theta y*Yau.realDifferenceQuotient i h
        (fun a ↦ eta a*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p a)) y) x j) := by
  let v : Yau.Jets.Coord → ℝ := fun y ↦ eta y*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p y)
  have hv : ContDiff ℝ ∞ v := he.mul (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p)
  have h1 := Yau.realGlobalCompactMap_ae (realFinCube_isCompact 4) theta ht.continuous hts _ _
    (Yau.realL2DifferenceMap_ae i h _ _ (sphereCutoffDerivativeMap_smooth_ae d p eta he hes j u))
  have h2 := Yau.realGlobalCompactMap_ae (realFinCube_isCompact 4) _
    (Yau.real_coordPartial_smooth theta ht j).continuous
    ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans hts) _ _
    (Yau.realL2DifferenceMap_ae i h _ _ (sphereCutoffValueMap_smooth_ae d p eta he hes u))
  apply ((Lp.coeFn_add _ _).trans (h1.add h2)).trans
  apply Filter.Eventually.of_forall
  intro x
  change theta x*Yau.realDifferenceQuotient i h (fun a ↦ Yau.coordPartial v a j) x +
    Yau.coordPartial theta x j*Yau.realDifferenceQuotient i h v x =
    Yau.coordPartial (fun a ↦ theta a*Yau.realDifferenceQuotient i h v a) x j
  rw [Yau.real_coordPartial_mul theta _ ht (Yau.realDifferenceQuotient_smooth i h v hv),
    Yau.realDifferenceQuotient_partial i j h v hv]
  ring

end
end Yau.Target

end OAI
