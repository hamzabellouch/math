import OAI.Geometry.NodalSets.Charts.SphereWeakThirdSymmetry

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_same_third_flux_symmetric (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d)
    (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
    (J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))))
    (hsecond : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
      (∫ x in Yau.realCenteredCube 4 (1/2), (sphereChartDerivativeMap d p a z) x*Yau.coordPartial psi x k)=
        -(∫ x in Yau.realCenteredCube 4 (1/2), H a k x*psi x))
    (hthird : ∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
      (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x i)=
        -(∫ x in Yau.realCenteredCube 4 (1/4), J a k i x*psi x)) :
    ∀ a k l, (J a k l : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict
      (interior (Yau.realCenteredCube 4 (1/4)))] J k l a := by
  have hs := sphere_same_third_derivatives_symmetric d p z H J hsecond hthird
  intro a k l
  exact (hs a k l).2.trans (hs k a l).1

end
end Yau.Target

end OAI
