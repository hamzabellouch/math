import OAI.Geometry.NodalSets.Charts.SphereChartDivergenceData
import OAI.Geometry.NodalSets.Elliptic.RealDifferenceQuotientTest
import OAI.Geometry.NodalSets.Elliptic.RealL2ZeroExtension

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section
local instance sphereChartFluxL2Measurable : MeasurableSpace Base := borel Base
local instance sphereChartFluxL2Borel : BorelSpace Base := ⟨rfl⟩

def sphereChartCompletedFlux (d : SphereEnergyData) (p : Base) (z : SphereEnergyHilbert d)
    (j : Fin 4) (x : Yau.Jets.Coord) : ℝ :=
  ∑ i, sphereChartPrincipalDensity d p x i j*(sphereChartDerivativeMap d p i z) x

theorem sphereChartCompletedFlux_memLp (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (j : Fin 4) :
    MemLp (sphereChartCompletedFlux d p z j) 2 (volume.restrict (realFinCube 4)) := by
  apply memLp_finsetSum
  intro i _
  obtain ⟨_,_,hb⟩ := Yau.real_compact_multiplier_bound (realFinCube_isCompact 4)
    (fun x ↦ sphereChartPrincipalDensity d p x i j) (sphereChartPrincipalDensity_smooth d p i j).continuous
  exact (hb _ (Lp.memLp (sphereChartDerivativeMap d p i z))).1

def sphereChartFluxZero (d : SphereEnergyData) (p : Base) (z : SphereEnergyHilbert d)
    (j : Fin 4) : Yau.Jets.Coord → ℝ :=
  (realFinCube 4).indicator (sphereChartCompletedFlux d p z j)

def sphereChartForcingZero (d : SphereEnergyData) (p : Base) (f : SphereWeightedL2 d) :
    Yau.Jets.Coord → ℝ := (realFinCube 4).indicator (sphereChartResolventForcing d p f)

theorem sphereChartFluxZero_memLp (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (j : Fin 4) : MemLp (sphereChartFluxZero d p z j) 2 volume :=
  (memLp_indicator_iff_restrict (realFinCube_isCompact 4).measurableSet).mpr
    (sphereChartCompletedFlux_memLp d p z j)

theorem sphereChartForcingZero_memLp (d : SphereEnergyData) (p : Base)
    (f : SphereWeightedL2 d) : MemLp (sphereChartForcingZero d p f) 2 volume := by
  obtain ⟨_,_,hb⟩ := sphereChartResolventForcing_bound d p (realFinCube_isCompact 4)
  exact (memLp_indicator_iff_restrict (realFinCube_isCompact 4).measurableSet).mpr (hb f).1

theorem sphere_resolvent_zeroFlux_test (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ realFinCube 4) :
    (∑ j, ∫ x, sphereChartFluxZero d p (sphereWeakSolution d f) j x*Yau.coordPartial phi x j) =
      ∫ x, sphereChartForcingZero d p f x*phi x := by
  have hi (j : Fin 4) : IntegrableOn (fun x ↦ sphereChartCompletedFlux d p (sphereWeakSolution d f) j x*
      Yau.coordPartial phi x j) (realFinCube 4) :=
    (sphereChartCompletedFlux_memLp d p (sphereWeakSolution d f) j).integrable_mul
      (Yau.real_continuous_memLp_compact (realFinCube_isCompact 4) _
        (Yau.real_coordPartial_smooth phi hp j).continuous)
  have h := (sphere_resolvent_divergence_weak d f p phi hp hc hs).2.2
  have hj (j : Fin 4) :
      (∫ x, sphereChartFluxZero d p (sphereWeakSolution d f) j x*Yau.coordPartial phi x j) =
      ∫ x in realFinCube 4, sphereChartCompletedFlux d p (sphereWeakSolution d f) j x*Yau.coordPartial phi x j := by
    rw [← integral_indicator (realFinCube_isCompact 4).measurableSet]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ (Set.indicator_mul_left (realFinCube 4)
      (sphereChartCompletedFlux d p (sphereWeakSolution d f) j) (fun x ↦ Yau.coordPartial phi x j)).symm)
  simp only [hj,sphereChartForcingZero,← Set.indicator_mul_left,
    integral_indicator (realFinCube_isCompact 4).measurableSet]
  rw [← integral_finsetSum Finset.univ (fun j _ ↦ hi j)]
  convert h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    simp only [sphereChartCompletedFlux,Finset.sum_mul]
    exact Finset.sum_comm)

end
end Yau.Target

end OAI
