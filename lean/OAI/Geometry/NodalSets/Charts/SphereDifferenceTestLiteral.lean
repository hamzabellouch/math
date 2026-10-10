import OAI.Geometry.NodalSets.Charts.SphereDifferenceTestEquation
import OAI.Geometry.NodalSets.Charts.SphereDifferenceTestWeak

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section
local instance sphereDifferenceLiteralMeasurable : MeasurableSpace Base := borel Base
local instance sphereDifferenceLiteralBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_resolvent_H1_difference_test_literal (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (r : ℝ) (hr : r ≤ 1)
    (hts : tsupport theta ⊆ Yau.realCenteredCube 4 r) (i : Fin 4) (h : ℝ) (hh : |h| ≤ 1-r) :
    let v := fun x ↦ eta x*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    let G := fun j x ↦ eta x*(sphereChartDerivativeMap d p j z) x+
      Yau.coordPartial eta x j*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    let phi := fun x ↦ theta x*Yau.realDifferenceQuotient i h v x
    let Psi := fun j x ↦ theta x*Yau.realDifferenceQuotient i h (G j) x+
      Yau.coordPartial theta x j*Yau.realDifferenceQuotient i h v x
    MemLp phi 2 volume ∧ (∀ j : Fin 4, MemLp (Psi j) 2 volume) ∧
    (∀ j : Fin 4, Integrable (fun x ↦
      Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*Psi j x)) ∧
    Integrable (fun x ↦ sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) ∧
    (∑ j, ∫ x, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*Psi j x) =
      -(∫ x, sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) := by
  dsimp only
  let hts' : tsupport theta ⊆ realFinCube 4 := hts.trans (Yau.realCenteredCube_mono hr)
  have hv := sphereDifferenceTestMap_ae d p eta theta he ht hes hts' i h z
  have hg (j : Fin 4) := sphereDifferenceTestDerivativeMap_ae d p eta theta he ht hes hts' i h j z
  have hb := sphere_resolvent_H1_difference_test d f p z eta theta he ht hes r hr hts i h hh
  dsimp only at hb
  have hd := Yau.realDifferenceQuotient_congr_ae i (-h) hv
  have hleft (j : Fin 4) :
      (fun x ↦ Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*
        (sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts' i h j z) x) =ᵐ[volume]
      (fun x ↦ Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*
        (theta x*Yau.realDifferenceQuotient i h
          (fun y ↦ eta y*(sphereChartDerivativeMap d p j z) y+
            Yau.coordPartial eta y j*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x+
          Yau.coordPartial theta x j*Yau.realDifferenceQuotient i h
            (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x)) :=
    Filter.EventuallyEq.rfl.mul (hg j)
  have hright := Filter.EventuallyEq.rfl.mul hd
    (f := sphereChartForcingZero d p f)
  refine ⟨(memLp_congr_ae hv).mp (Lp.memLp _),
    fun j ↦ (memLp_congr_ae (hg j)).mp (Lp.memLp _),
    fun j ↦ (hb.1 j).congr (hleft j),hb.2.1.congr hright,?_⟩
  have h0 := hb.2.2
  simp only [integral_congr_ae (hleft _)] at h0
  exact h0.trans (congrArg Neg.neg (integral_congr_ae hright))

end
end Yau.Target

end OAI
