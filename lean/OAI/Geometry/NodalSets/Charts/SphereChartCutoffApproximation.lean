import OAI.Geometry.NodalSets.Charts.SphereChartCutoffWeak
import OAI.Geometry.NodalSets.Charts.SphereChartStrongApproximation
import OAI.Geometry.NodalSets.Elliptic.RealCompactL2MapLemmas

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section
local instance sphereChartCutoffApproxMeasurable : MeasurableSpace Base := borel Base
local instance sphereChartCutoffApproxBorel : BorelSpace Base := ⟨rfl⟩

def sphereCutoffValueMap (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) :
    SphereEnergyHilbert d →L[ℝ] Yau.RealEuclideanL2 4 :=
  (Yau.realCompactL2Map (realFinCube_isCompact 4) eta he.continuous hs).comp
    ((sphereChartValueMap d p).comp (sphereEnergyL2Map d))

def sphereCutoffDerivativeMap (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (i : Fin 4) :
    SphereEnergyHilbert d →L[ℝ] Yau.RealEuclideanL2 4 :=
  (Yau.realCompactL2Map (realFinCube_isCompact 4) eta he.continuous hs).comp
    (sphereChartDerivativeMap d p i) +
  (Yau.realCompactL2Map (realFinCube_isCompact 4) (fun x ↦ Yau.coordPartial eta x i)
    (Yau.real_coordPartial_smooth eta he i).continuous
    ((tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs)).comp
    ((sphereChartValueMap d p).comp (sphereEnergyL2Map d))

theorem sphereCutoffValueMap_ae (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (z : SphereEnergyHilbert d) :
    (sphereCutoffValueMap d p eta he hs z : Yau.Jets.Coord → ℝ) =ᵐ[volume]
      (fun x ↦ eta x*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)) :=
  (Yau.realCompactL2Map_ae (realFinCube_isCompact 4) eta he.continuous hs _).trans
    (Yau.real_compact_mul_ae (realFinCube_isCompact 4).measurableSet eta _ _ hs
      (sphereChartValueMap_ae d p (sphereEnergyL2Map d z)))

theorem sphereCutoffDerivativeMap_ae (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (i : Fin 4) (z : SphereEnergyHilbert d) :
    (sphereCutoffDerivativeMap d p eta he hs i z : Yau.Jets.Coord → ℝ) =ᵐ[volume]
      (fun x ↦ eta x*(sphereChartDerivativeMap d p i z) x+
        Yau.coordPartial eta x i*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)) := by
  have hd := (tsupport_fderiv_apply_subset ℝ (Pi.single i 1) (f := eta)).trans hs
  have h1 := Yau.realCompactL2Map_ae (realFinCube_isCompact 4) eta he.continuous hs
    (sphereChartDerivativeMap d p i z)
  have h2 := (Yau.realCompactL2Map_ae (realFinCube_isCompact 4) _
    (Yau.real_coordPartial_smooth eta he i).continuous hd
    (sphereChartValueMap d p (sphereEnergyL2Map d z))).trans
      (Yau.real_compact_mul_ae (realFinCube_isCompact 4).measurableSet _ _ _ hd
        (sphereChartValueMap_ae d p (sphereEnergyL2Map d z)))
  exact (Lp.coeFn_add _ _).trans (h1.add h2)

theorem sphereCutoffValueMap_smooth_ae (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (u : SphereEnergySmooth d) :
    (sphereCutoffValueMap d p eta he hs (sphereEnergyToCompletion d u) : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] (fun x ↦ eta x*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p x)) :=
  (Yau.realCompactL2Map_ae (realFinCube_isCompact 4) eta he.continuous hs _).trans
    (Yau.real_compact_mul_ae (realFinCube_isCompact 4).measurableSet eta _ _ hs
      (sphereChartValueMap_coe_ae d p u))

theorem sphereCutoffDerivativeMap_smooth_ae (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (i : Fin 4) (u : SphereEnergySmooth d) :
    (sphereCutoffDerivativeMap d p eta he hs i (sphereEnergyToCompletion d u) : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] (fun x ↦ Yau.coordPartial
        (fun y ↦ eta y*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p y)) x i) := by
  have hd := (tsupport_fderiv_apply_subset ℝ (Pi.single i 1) (f := eta)).trans hs
  have hpart : (sphereChartDerivativeMap d p i (sphereEnergyToCompletion d u) : Yau.Jets.Coord → ℝ)
      =ᵐ[volume.restrict (realFinCube 4)] sphereSmoothChartPartial d p i u := by
    rw [sphereChartDerivativeMap_coe]
    exact (sphereSmoothChartPartial_memLp d p i u).coeFn_toLp
  have h1 := (Yau.realCompactL2Map_ae (realFinCube_isCompact 4) eta he.continuous hs
    (sphereChartDerivativeMap d p i (sphereEnergyToCompletion d u))).trans
      (Yau.real_compact_mul_ae (realFinCube_isCompact 4).measurableSet eta _ _ hs hpart)
  have h2 := (Yau.realCompactL2Map_ae (realFinCube_isCompact 4) _
    (Yau.real_coordPartial_smooth eta he i).continuous hd
    (sphereChartValueMap d p (sphereEnergyL2Map d (sphereEnergyToCompletion d u)))).trans
      (Yau.real_compact_mul_ae (realFinCube_isCompact 4).measurableSet _ _ _ hd
        (sphereChartValueMap_coe_ae d p u))
  apply ((Lp.coeFn_add _ _).trans (h1.add h2)).trans
  apply Filter.Eventually.of_forall
  intro x
  have hp := Yau.real_coordPartial_mul eta _ he
    (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p) x i
  simp only [Function.comp_def] at hp
  simp only [Pi.add_apply,sphereSmoothChartPartial,Function.comp_def]
  rw [hp]
  ring

theorem sphere_chart_cutoff_strong_approximation (d : SphereEnergyData)
    (z : SphereEnergyHilbert d) :
    ∃ u : ℕ → SphereEnergySmooth d,
      Tendsto (fun n ↦ sphereEnergyToCompletion d (u n)) atTop (𝓝 z) ∧
      ∀ (p : Base) (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
        (hs : tsupport eta ⊆ realFinCube 4),
        Tendsto (fun n ↦ sphereCutoffValueMap d p eta he hs (sphereEnergyToCompletion d (u n)))
          atTop (𝓝 (sphereCutoffValueMap d p eta he hs z)) ∧
        ∀ i : Fin 4, Tendsto
          (fun n ↦ sphereCutoffDerivativeMap d p eta he hs i (sphereEnergyToCompletion d (u n)))
          atTop (𝓝 (sphereCutoffDerivativeMap d p eta he hs i z)) := by
  obtain ⟨u,hu,_⟩ := sphere_chart_strong_approximation d z
  refine ⟨u,hu,fun p eta he hs ↦ ⟨?_,fun i ↦ ?_⟩⟩
  · exact (sphereCutoffValueMap d p eta he hs).continuous.continuousAt.tendsto.comp hu
  · exact (sphereCutoffDerivativeMap d p eta he hs i).continuous.continuousAt.tendsto.comp hu

end
end Yau.Target

end OAI
