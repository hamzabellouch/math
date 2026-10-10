import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakRestrictionLemmas
import OAI.Geometry.NodalSets.Elliptic.RealWeakHessianSymmetry
import OAI.Geometry.NodalSets.Spectral.SphereResolventInteriorH2

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_chart_weak_hessian_symmetric (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d)
    (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
    (hsecond : ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
      (∫ x in Yau.realCenteredCube 4 (1/2), (sphereChartDerivativeMap d p a z) x*Yau.coordPartial psi x i) =
        -(∫ x in Yau.realCenteredCube 4 (1/2), H a i x*psi x)) (a i : Fin 4) :
    (H a i : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict (interior (Yau.realCenteredCube 4 (1/2)))] H i a := by
  let w := fun x ↦ (sphereEnergyL2Map d z) (sphereChartCoordMap p x)
  have hK := Yau.realCenteredCube_isCompact 4 (1/2:ℝ)
  have hsub : Yau.realCenteredCube 4 (1/2) ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  obtain ⟨_,_,hb⟩ := sphereWeightedL2_compact_chart_bound d p (realFinCube_isCompact 4)
  have hfirst (j : Fin 4) := Yau.real_interior_weak_restrict hK (realFinCube_isCompact 4).measurableSet hsub
    w (sphereChartDerivativeMap d p j z) (hb (sphereEnergyL2Map d z)).1 (Lp.memLp _) j
    (fun psi hp hc hs ↦ by
      have hw := (sphere_chart_weak_derivative d p j z psi hp hc hs).2.2
      change (∫ x in realFinCube 4, (sphereChartDerivativeMap d p j z) x*psi x) =
        -(∫ x in realFinCube 4, w x*Yau.coordPartial psi x j) at hw
      linarith only [hw])
  exact Yau.real_weak_hessian_symmetry hK w (fun a ↦ sphereChartDerivativeMap d p a z)
    (fun a i ↦ H a i) (fun a i ↦ Lp.memLp (H a i))
    (fun a psi hp hc hs ↦ ((hfirst a).2.2 psi hp hc hs).2.2) hsecond a i

theorem sphere_resolvent_actual_hessian_symmetric (d : SphereEnergyData) (p : Base) :
    ∃ C1 > 0, ∀ f : SphereWeightedL2 d,
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))),
        (∑ a, ∑ i, ‖H a i‖^2) ≤ C1*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          (∫ x in Yau.realCenteredCube 4 (1/2),
            (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/2), H a i x*psi x)) ∧
        ∀ a i, (H a i : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict
          (interior (Yau.realCenteredCube 4 (1/2)))] H i a := by
  obtain ⟨C1,hC1,hH⟩ := sphere_resolvent_interior_second_weak_derivatives d p
  refine ⟨C1,hC1,fun f ↦ ?_⟩
  obtain ⟨H,hb,hw⟩ := hH f
  have he := fun a i psi hp hc hs ↦ (hw a i psi hp hc hs).2.2
  exact ⟨H,hb,he,fun a i ↦ sphere_chart_weak_hessian_symmetric d p (sphereWeakSolution d f) H he a i⟩

end
end Yau.Target

end OAI
