import OAI.Geometry.NodalSets.Charts.SphereChartWeakDerivative

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section
local instance sphereChartWeakDivergenceMeasurable : MeasurableSpace Base := borel Base
local instance sphereChartWeakDivergenceBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_chart_weak_divergence (d : SphereEnergyData) (p : Base) (z : SphereEnergyHilbert d)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ V x i))
    (hs : ∀ i, tsupport (fun x ↦ V x i) ⊆ realFinCube 4) :
    IntegrableOn (fun x ↦ ∑ i, (sphereChartDerivativeMap d p i z) x*V x i) (realFinCube 4) ∧
    IntegrableOn (fun x ↦ (sphereEnergyL2Map d z) (sphereChartCoordMap p x)*Yau.coordDiv V x)
      (realFinCube 4) ∧
    (∫ x in realFinCube 4, ∑ i, (sphereChartDerivativeMap d p i z) x*V x i) =
      -(∫ x in realFinCube 4, (sphereEnergyL2Map d z) (sphereChartCoordMap p x)*Yau.coordDiv V x) := by
  have h (i : Fin 4) := sphere_chart_weak_derivative d p i z (fun x ↦ V x i) (hV i) (hc i) (hs i)
  have hleft := integrable_finsetSum Finset.univ (fun i _ ↦ (h i).1)
  have hright := integrable_finsetSum Finset.univ (fun i _ ↦ (h i).2.1)
  have he : (fun x ↦ (sphereEnergyL2Map d z) (sphereChartCoordMap p x)*Yau.coordDiv V x) =
      (fun x ↦ ∑ i, (sphereEnergyL2Map d z) (sphereChartCoordMap p x)*Yau.coordPartial (fun y ↦ V y i) x i) := by
    funext x
    simp only [Yau.coordDiv,Finset.mul_sum]
  rw [he]
  refine ⟨hleft,hright,?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ (h i).1),integral_finsetSum _ (fun i _ ↦ (h i).2.1)]
  simp only [(h _).2.2,Finset.sum_neg_distrib]

end
end Yau.Target

end OAI
