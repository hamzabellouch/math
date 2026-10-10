import OAI.Geometry.NodalSets.Charts.SphereDifferenceTestMaps
import OAI.Geometry.NodalSets.Elliptic.RealL2PairingRepresentatives
import OAI.Geometry.NodalSets.Spectral.SphereResolventDifferenceEquation

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section
local instance sphereDifferenceEquationMeasurable : MeasurableSpace Base := borel Base
local instance sphereDifferenceEquationBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_resolvent_H1_difference_test (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (r : ℝ) (hr : r ≤ 1)
    (hts : tsupport theta ⊆ Yau.realCenteredCube 4 r) (i : Fin 4) (h : ℝ) (hh : |h| ≤ 1-r) :
    let hts' : tsupport theta ⊆ realFinCube 4 := hts.trans (Yau.realCenteredCube_mono hr)
    let T := sphereDifferenceTestMap d p eta theta he ht hes hts' i h
    let D := sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts' i h
    (∀ j : Fin 4, Integrable (fun x ↦
      Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*(D j z) x)) ∧
    Integrable (fun x ↦ sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) (T z) x) ∧
    (∑ j, ∫ x, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*(D j z) x) =
      -(∫ x, sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) (T z) x) := by
  dsimp only
  let hts' : tsupport theta ⊆ realFinCube 4 := hts.trans (Yau.realCenteredCube_mono hr)
  let T := sphereDifferenceTestMap d p eta theta he ht hes hts' i h
  let D := sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts' i h
  let A : Fin 4 → Yau.RealEuclideanL2 4 := fun j ↦
    (Yau.realDifferenceQuotient_memLp i h _ (sphereChartFluxZero_memLp d p (sphereWeakSolution d f) j)).toLp
      (Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j))
  let F : Yau.RealEuclideanL2 4 := (sphereChartForcingZero_memLp d p f).toLp (sphereChartForcingZero d p f)
  have ha (j : Fin 4) : (A j : Yau.Jets.Coord → ℝ) =ᵐ[volume]
      Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) :=
    (Yau.realDifferenceQuotient_memLp i h _ (sphereChartFluxZero_memLp d p (sphereWeakSolution d f) j)).coeFn_toLp
  have hf : (F : Yau.Jets.Coord → ℝ) =ᵐ[volume] sphereChartForcingZero d p f :=
    (sphereChartForcingZero_memLp d p f).coeFn_toLp
  have hid (w : SphereEnergyHilbert d) : (∑ j, inner ℝ (A j) (D j w)) =
      -inner ℝ F (Yau.realL2DifferenceMap i (-h) (T w)) := by
    apply (sphereEnergyToCompletion_dense d).induction_on
      (p := fun w ↦ (∑ j, inner ℝ (A j) (D j w)) = -inner ℝ F (Yau.realL2DifferenceMap i (-h) (T w))) w
    · apply isClosed_eq
      · exact continuous_finsetSum _ (fun j _ ↦ continuous_const.inner (D j).continuous)
      · exact (continuous_const.inner ((Yau.realL2DifferenceMap i (-h)).continuous.comp T.continuous)).neg
    · intro u
      let v : Yau.Jets.Coord → ℝ := fun y ↦ eta y*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p y)
      let phi : Yau.Jets.Coord → ℝ := fun x ↦ theta x*Yau.realDifferenceQuotient i h v x
      have hv : ContDiff ℝ ∞ v := he.mul (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p)
      have hp : ContDiff ℝ ∞ phi := ht.mul (Yau.realDifferenceQuotient_smooth i h v hv)
      have hct : HasCompactSupport theta :=
        (Yau.realCenteredCube_isCompact 4 r).of_isClosed_subset (isClosed_tsupport theta) hts
      have hc : HasCompactSupport phi := hct.mul_right
      have hs : tsupport phi ⊆ Yau.realCenteredCube 4 r := tsupport_mul_subset_left.trans hts
      have eq := (sphere_resolvent_difference_equation_radius d f p i r hr h hh phi hp hc hs).2.2
      have ht0 := sphereDifferenceTestMap_smooth_ae d p eta theta he ht hes hts' i h u
      have hd0 (j : Fin 4) := sphereDifferenceTestDerivativeMap_smooth_ae d p eta theta he ht hes hts' i h j u
      have hleft (j : Fin 4) : inner ℝ (A j) (D j (sphereEnergyToCompletion d u)) =
          ∫ x, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*
            Yau.coordPartial phi x j :=
        (Yau.real_L2_inner_reps _ _ _ _ (ha j) (hd0 j)).2
      have hright : inner ℝ F (Yau.realL2DifferenceMap i (-h) (T (sphereEnergyToCompletion d u))) =
          ∫ x, sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x :=
        (Yau.real_L2_inner_reps _ _ _ _ hf (Yau.realL2DifferenceMap_ae i (-h) _ _ ht0)).2
      simp only [hleft,hright]
      exact eq
  have hl (j : Fin 4) := Yau.real_L2_inner_reps (A j) (D j z) _ _ (ha j) Filter.EventuallyEq.rfl
  have hr' := Yau.real_L2_inner_reps F (Yau.realL2DifferenceMap i (-h) (T z)) _ _ hf
    (Yau.realL2DifferenceMap_ae i (-h) (T z) (T z) Filter.EventuallyEq.rfl)
  refine ⟨fun j ↦ (hl j).1,hr'.1,?_⟩
  have h0 := hid z
  simpa only [(hl _).2,hr'.2] using h0

end
end Yau.Target

end OAI
