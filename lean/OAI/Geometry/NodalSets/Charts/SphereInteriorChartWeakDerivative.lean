import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakRestrictionLemmas
import OAI.Geometry.NodalSets.Spectral.SphereEigenResolventForcing

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_resolvent_interior_first_pairing (d : SphereEnergyData) (p : Base)
    (f : SphereWeightedL2 d) {K : Set Yau.Jets.Coord}
    (hK : IsCompact K) (hsub : K ⊆ realFinCube 4) (a : Fin 4) :
    MemLp (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)) 2 (volume.restrict K) ∧
    MemLp (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) 2 (volume.restrict K) ∧
    ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      IntegrableOn (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)*Yau.coordPartial psi x a) K ∧
      IntegrableOn (fun x ↦ (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*psi x) K ∧
      (∫ x in K, (sphereL2Resolvent d f) (sphereChartCoordMap p x)*Yau.coordPartial psi x a) =
        -(∫ x in K, (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*psi x) := by
  obtain ⟨_,_,hb⟩ := sphereWeightedL2_compact_chart_bound d p (realFinCube_isCompact 4)
  apply Yau.real_interior_weak_restrict hK (realFinCube_isCompact 4).measurableSet hsub
    _ _ (hb (sphereL2Resolvent d f)).1 (Lp.memLp _) a
  intro psi hp hc hs
  have h := (sphere_chart_weak_derivative d p a (sphereWeakSolution d f) psi hp hc hs).2.2
  change (∫ x in realFinCube 4, (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*psi x) =
    -(∫ x in realFinCube 4, (sphereL2Resolvent d f) (sphereChartCoordMap p x)*Yau.coordPartial psi x a) at h
  linarith only [h]

end
end Yau.Target

end OAI
