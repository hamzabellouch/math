import OAI.Geometry.NodalSets.Charts.SphereChartFluxL2
import OAI.Geometry.NodalSets.Elliptic.RealBallCubeContainmentLemmas

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
noncomputable section

theorem sphereChartFluxZero_difference_expansion (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (i j : Fin 4) (h : ℝ) (x : Yau.Jets.Coord)
    (hx : x ∈ realFinCube 4) (ht : x+Pi.single i h ∈ realFinCube 4) :
    Yau.realDifferenceQuotient i h (sphereChartFluxZero d p z j) x =
      ∑ a, (sphereChartPrincipalDensity d p (x+Pi.single i h) a j*
          Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p a z) x+
        Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x*
          (sphereChartDerivativeMap d p a z) x) := by
  have he : Yau.realDifferenceQuotient i h (sphereChartFluxZero d p z j) x =
      Yau.realDifferenceQuotient i h (sphereChartCompletedFlux d p z j) x := by
    simp only [Yau.realDifferenceQuotient,sphereChartFluxZero,indicator_of_mem hx,indicator_of_mem ht]
  rw [he]
  unfold sphereChartCompletedFlux
  rw [Yau.realDifferenceQuotient_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact Yau.realDifferenceQuotient_mul i h _ _ x

end
end Yau.Target

end OAI
