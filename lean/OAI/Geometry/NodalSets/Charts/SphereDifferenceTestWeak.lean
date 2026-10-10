import OAI.Geometry.NodalSets.Charts.SphereDifferenceTestMaps
import OAI.Geometry.NodalSets.Elliptic.RealL2PairingRepresentatives

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

theorem sphere_difference_test_strong_approximation (d : SphereEnergyData) (z : SphereEnergyHilbert d) :
    ∃ u : ℕ → SphereEnergySmooth d,
      Tendsto (fun n ↦ sphereEnergyToCompletion d (u n)) atTop (𝓝 z) ∧
      ∀ (p : Base) (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
        (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4) (i : Fin 4) (h : ℝ),
        Tendsto (fun n ↦ sphereDifferenceTestMap d p eta theta he ht hes hts i h (sphereEnergyToCompletion d (u n)))
          atTop (𝓝 (sphereDifferenceTestMap d p eta theta he ht hes hts i h z)) ∧
        ∀ j : Fin 4, Tendsto
          (fun n ↦ sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j (sphereEnergyToCompletion d (u n)))
          atTop (𝓝 (sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j z)) := by
  obtain ⟨u,hu,_⟩ := sphere_chart_strong_approximation d z
  refine ⟨u,hu,fun p eta theta he ht hes hts i h ↦ ⟨?_,fun j ↦ ?_⟩⟩
  · exact (sphereDifferenceTestMap d p eta theta he ht hes hts i h).continuous.continuousAt.tendsto.comp hu
  · exact (sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j).continuous.continuousAt.tendsto.comp hu

theorem sphere_difference_test_weak (d : SphereEnergyData) (p : Base) (z : SphereEnergyHilbert d)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (j : Fin 4) (phi : Yau.Jets.Coord → ℝ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    let T := sphereDifferenceTestMap d p eta theta he ht hes hts i h
    let D := sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j
    Integrable (fun x ↦ (D z) x*phi x) ∧
    Integrable (fun x ↦ (T z) x*Yau.coordPartial phi x j) ∧
    (∫ x, (D z) x*phi x) = -(∫ x, (T z) x*Yau.coordPartial phi x j) := by
  dsimp only
  let T := sphereDifferenceTestMap d p eta theta he ht hes hts i h
  let D := sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j
  let hm := Yau.real_compact_continuous_memLp phi hp.continuous hc
  let hn := Yau.real_compact_continuous_memLp _ (Yau.real_coordPartial_smooth phi hp j).continuous
    (hc.fderiv_apply ℝ (Pi.single j 1))
  let P := hm.toLp phi
  let Q := hn.toLp (fun x ↦ Yau.coordPartial phi x j)
  have hid : inner ℝ (D z) P = -inner ℝ (T z) Q := by
    apply (sphereEnergyToCompletion_dense d).induction_on
      (p := fun w ↦ inner ℝ (D w) P = -inner ℝ (T w) Q) z
    · exact isClosed_eq (D.continuous.inner continuous_const) (T.continuous.inner continuous_const).neg
    · intro u
      let v : Yau.Jets.Coord → ℝ := fun x ↦ eta x*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p x)
      let a : Yau.Jets.Coord → ℝ := fun x ↦ theta x*Yau.realDifferenceQuotient i h v x
      have hv : ContDiff ℝ ∞ v := he.mul (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p)
      have ha : ContDiff ℝ ∞ a := ht.mul (Yau.realDifferenceQuotient_smooth i h v hv)
      have h1 := (Yau.real_L2_inner_reps _ _ _ _
        (sphereDifferenceTestDerivativeMap_smooth_ae d p eta theta he ht hes hts i h j u) hm.coeFn_toLp).2
      have h2 := (Yau.real_L2_inner_reps _ _ _ _
        (sphereDifferenceTestMap_smooth_ae d p eta theta he ht hes hts i h u) hn.coeFn_toLp).2
      rw [h1,h2]
      simpa only [Measure.restrict_univ] using
        (Yau.real_compact_test_derivative a phi ha hp hc j univ (subset_univ _)).2.2
  have h1 := Yau.real_L2_test_pairing (D z) phi hm
  have h2 := Yau.real_L2_test_pairing (T z) (fun x ↦ Yau.coordPartial phi x j) hn
  exact ⟨h1.1,h2.1,by rw [← h1.2,← h2.2]; exact hid⟩

end
end Yau.Target

end OAI
