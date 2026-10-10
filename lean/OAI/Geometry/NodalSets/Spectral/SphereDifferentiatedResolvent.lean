import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakRestrictionLemmas
import OAI.Geometry.NodalSets.Spectral.SphereInteriorResolventEquation
import OAI.Geometry.NodalSets.Spectral.SphereResolventInteriorH2

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_resolvent_differentiated_equation (d : SphereEnergyData) (p : Base) :
    ∃ C1 > 0, ∀ f : SphereWeightedL2 d,
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))),
        (∑ a : Fin 4, ∑ i : Fin 4, ‖H a i‖^2) ≤ C1*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ (a i : Fin 4) (psi : Yau.Jets.Coord → ℝ),
          ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          IntegrableOn (fun x ↦ (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*
            Yau.coordPartial psi x i) (Yau.realCenteredCube 4 (1/2)) ∧
          IntegrableOn (fun x ↦ H a i x*psi x) (Yau.realCenteredCube 4 (1/2)) ∧
          (∫ x in Yau.realCenteredCube 4 (1/2),
            (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/2), H a i x*psi x)) ∧
        ∀ (k : Fin 4) (psi : Yau.Jets.Coord → ℝ),
          ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          (∀ a j, IntegrableOn (fun x ↦ sphereChartPrincipalDensity d p x a j*H a k x*
            Yau.coordPartial psi x j) (Yau.realCenteredCube 4 (1/2)) ∧
            IntegrableOn (fun x ↦ Yau.coordPartial (fun y ↦ sphereChartPrincipalDensity d p y a j) x k*
              (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x j)
              (Yau.realCenteredCube 4 (1/2))) ∧
          IntegrableOn (fun x ↦ sphereChartResolventForcing d p f x*Yau.coordPartial psi x k)
            (Yau.realCenteredCube 4 (1/2)) ∧
          (∑ a, ∑ j, ∫ x in Yau.realCenteredCube 4 (1/2),
            sphereChartPrincipalDensity d p x a j*H a k x*Yau.coordPartial psi x j) =
            -(∫ x in Yau.realCenteredCube 4 (1/2),
              sphereChartResolventForcing d p f x*Yau.coordPartial psi x k) -
            ∑ a, ∑ j, ∫ x in Yau.realCenteredCube 4 (1/2),
              Yau.coordPartial (fun y ↦ sphereChartPrincipalDensity d p y a j) x k*
                (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x j := by
  obtain ⟨C1,hC1,hH⟩ := sphere_resolvent_interior_second_weak_derivatives d p
  refine ⟨C1,hC1,fun f ↦ ?_⟩
  obtain ⟨H,hb,hw⟩ := hH f
  refine ⟨H,hb,hw,fun k psi hp hc hs ↦ ?_⟩
  have hK := Yau.realCenteredCube_isCompact 4 (1/2:ℝ)
  have hsub : Yau.realCenteredCube 4 (1/2) ⊆ realFinCube 4 :=
    Yau.realCenteredCube_mono (by norm_num)
  obtain ⟨_,_,hF⟩ := sphereChartResolventForcing_bound d p hK
  exact Yau.real_weak_equation_differentiation hK (sphereChartPrincipalDensity d p)
    (fun a ↦ sphereChartDerivativeMap d p a (sphereWeakSolution d f)) (fun a k ↦ H a k)
    (sphereChartResolventForcing d p f) (sphereChartPrincipalDensity_smooth d p)
    (fun a ↦ (Lp.memLp _).mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun a k ↦ Lp.memLp (H a k)) (hF f).1
    (fun a k psi hp hc hs ↦ (hw a k psi hp hc hs).2.2)
    (fun psi hp hc hs ↦ (sphere_resolvent_interior_equation d f p hK hsub psi hp hc hs).2.2)
    k psi hp hc hs

end
end Yau.Target

end OAI
