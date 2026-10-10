import OAI.Geometry.NodalSets.Charts.SphereChartFluxL2

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section
local instance sphereResolventDifferenceEquationMeasurable : MeasurableSpace Base := borel Base
local instance sphereResolventDifferenceEquationBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_resolvent_difference_equation_radius (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (i : Fin 4) (r : ℝ) (hr : r ≤ 1) (h : ℝ) (hh : |h| ≤ 1-r)
    (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Yau.realCenteredCube 4 r) :
    (∀ j : Fin 4, Integrable (fun x ↦
      Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*
        Yau.coordPartial phi x j)) ∧
    Integrable (fun x ↦ sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) ∧
    (∑ j, ∫ x, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*
      Yau.coordPartial phi x j) =
      -(∫ x, sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) := by
  have htest := sphere_resolvent_zeroFlux_test d f p (Yau.realDifferenceQuotient i (-h) phi)
    (Yau.realDifferenceQuotient_smooth i (-h) phi hp)
    (Yau.realDifferenceQuotient_compact i (-h) phi hc)
    (Yau.realDifferenceQuotient_tsupport i (-h) phi (realFinCube_isCompact 4).isClosed
      (hs.trans (Yau.realCenteredCube_mono hr))
      (fun x hx ↦ Yau.realCenteredCube_shift i (by simpa only [abs_neg] using hh) (hs hx)))
  have hd (j : Fin 4) := Yau.real_differenceQuotient_pairing i h
    (sphereChartFluxZero d p (sphereWeakSolution d f) j) (fun x ↦ Yau.coordPartial phi x j)
    (sphereChartFluxZero_memLp d p (sphereWeakSolution d f) j)
    (Yau.real_compact_continuous_memLp _ (Yau.real_coordPartial_smooth phi hp j).continuous
      (hc.fderiv_apply ℝ (Pi.single j 1)))
  have hi := (sphereChartForcingZero_memLp d p f).integrable_mul
    (Yau.realDifferenceQuotient_memLp i (-h) phi (Yau.real_compact_continuous_memLp phi hp.continuous hc))
  refine ⟨fun j ↦ (hd j).1,hi,?_⟩
  simp only [Yau.realDifferenceQuotient_partial i _ (-h) phi hp] at htest
  simp only [(hd _).2.2,Finset.sum_neg_distrib]
  exact congrArg Neg.neg htest

theorem sphere_resolvent_difference_equation (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (i : Fin 4) (h : ℝ) (hh : |h| ≤ 1/2)
    (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Yau.realCenteredCube 4 (1/2)) :
    (∀ j : Fin 4, Integrable (fun x ↦
      Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*
        Yau.coordPartial phi x j)) ∧
    Integrable (fun x ↦ sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) ∧
    (∑ j, ∫ x, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*
      Yau.coordPartial phi x j) =
      -(∫ x, sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) := by
  exact sphere_resolvent_difference_equation_radius d f p i (1/2) (by norm_num) h (by linarith) phi hp hc hs

end
end Yau.Target

end OAI
