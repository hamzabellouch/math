import OAI.Geometry.NodalSets.Charts.SphereDifferenceTestWeak
import OAI.Geometry.NodalSets.Elliptic.RealSmoothDifferenceBound

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_difference_test_difference_bound (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (j : Fin 4) (t : ℝ) :
    ‖Yau.realL2DifferenceMap j t (sphereDifferenceTestMap d p eta theta he ht hes hts i h z)‖^2 ≤
      ‖sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j z‖^2 := by
  obtain ⟨u,_,hu⟩ := sphere_difference_test_strong_approximation d z
  apply Yau.real_difference_norm_bound_limit j t _ _ _ _
    (hu p eta theta he ht hes hts i h).1 ((hu p eta theta he ht hes hts i h).2 j)
  intro k
  let v : Yau.Jets.Coord → ℝ := fun x ↦ eta x*(SphereEnergySmooth.toSmooth d (u k) : Base → ℝ) (sphereChartCoordMap p x)
  let phi : Yau.Jets.Coord → ℝ := fun x ↦ theta x*Yau.realDifferenceQuotient i h v x
  have hv : ContDiff ℝ ∞ v := he.mul (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d (u k)).property p)
  have hp : ContDiff ℝ ∞ phi := ht.mul (Yau.realDifferenceQuotient_smooth i h v hv)
  have hc : HasCompactSupport theta := (realFinCube_isCompact 4).of_isClosed_subset (isClosed_tsupport theta) hts
  have hval := sphereDifferenceTestMap_smooth_ae d p eta theta he ht hes hts i h (u k)
  have hder := sphereDifferenceTestDerivativeMap_smooth_ae d p eta theta he ht hes hts i h j (u k)
  rw [Yau.real_L2_norm_sq_rep _ _ (Yau.realL2DifferenceMap_ae j t _ _ hval),
    Yau.real_L2_norm_sq_rep _ _ hder]
  exact (Yau.real_smooth_difference_bound phi hp hc.mul_right j t).2

end
end Yau.Target

end OAI
