import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakAddLemmas
import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakRestrictionLemmas
import OAI.Geometry.NodalSets.Spectral.SphereDifferentiatedResolvent
import OAI.Geometry.NodalSets.Spectral.SphereEigenResolventForcing

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_eigen_differentiated_equation (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) :
    ∃ C1 > 0, ∀ (mu : ℝ), mu ≠ 0 → ∀ (f : SphereWeightedL2 d),
      sphereL2Resolvent d f=mu • f →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))),
        (∑ a, ∑ i, ‖H a i‖^2) ≤ C1*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          (∫ x in Yau.realCenteredCube 4 (1/2),
            (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/2), H a i x*psi x)) ∧
        ∀ k : Fin 4,
          let U := fun a ↦ (sphereChartDerivativeMap d p a (sphereWeakSolution d f) : Yau.Jets.Coord → ℝ)
          let G := Yau.realWeakGradientCommutator (sphereChartPrincipalDensity d p) U k
          let DG := Yau.realWeakGradientCommutatorDerivative (sphereChartPrincipalDensity d p) U
            (fun a i ↦ H a i) k
          MemLp (sphereEigenForcingDerivative d p mu f k) 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))) ∧
          (∀ j l, MemLp (G j) 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))) ∧
            MemLp (DG j l) 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))) ∧
            ∀ psi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
              tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
              IntegrableOn (fun x ↦ G j x*Yau.coordPartial psi x l) (Yau.realCenteredCube 4 (1/2)) ∧
              IntegrableOn (fun x ↦ DG j l x*psi x) (Yau.realCenteredCube 4 (1/2)) ∧
              (∫ x in Yau.realCenteredCube 4 (1/2), G j x*Yau.coordPartial psi x l) =
                -(∫ x in Yau.realCenteredCube 4 (1/2), DG j l x*psi x)) ∧
          ∀ psi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
            tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
            (∀ a j, IntegrableOn (fun x ↦ sphereChartPrincipalDensity d p x a j*H a k x*
              Yau.coordPartial psi x j) (Yau.realCenteredCube 4 (1/2))) ∧
            IntegrableOn (fun x ↦ sphereEigenForcingDerivative d p mu f k x*psi x)
              (Yau.realCenteredCube 4 (1/2)) ∧
            (∀ j, IntegrableOn (fun x ↦ G j x*Yau.coordPartial psi x j) (Yau.realCenteredCube 4 (1/2))) ∧
            (∑ a, ∑ j, ∫ x in Yau.realCenteredCube 4 (1/2),
              sphereChartPrincipalDensity d p x a j*H a k x*Yau.coordPartial psi x j) =
              (∫ x in Yau.realCenteredCube 4 (1/2), sphereEigenForcingDerivative d p mu f k x*psi x)-
                ∑ j, ∫ x in Yau.realCenteredCube 4 (1/2), G j x*Yau.coordPartial psi x j := by
  obtain ⟨C1,hC1,hH⟩ := sphere_resolvent_differentiated_equation d p
  refine ⟨C1,hC1,fun mu hmu f he ↦ ?_⟩
  obtain ⟨H,hb,hw,heq⟩ := hH f
  refine ⟨H,hb,(fun a i psi hp hc hs ↦ (hw a i psi hp hc hs).2.2),fun k ↦ ?_⟩
  dsimp only
  have hK := Yau.realCenteredCube_isCompact 4 (1/2:ℝ)
  have hsub : Yau.realCenteredCube 4 (1/2) ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  have hF := sphere_eigen_resolvent_forcing_H1 d p hrho mu hmu f he k
  have hFK := Yau.real_interior_weak_restrict hK (realFinCube_isCompact 4).measurableSet hsub
    _ _ hF.1 hF.2.1 k (fun psi hp hc hs ↦ (hF.2.2 psi hp hc hs).2.2)
  have hG (j l : Fin 4) := Yau.real_weak_gradient_commutator_H1 hK (sphereChartPrincipalDensity d p)
    (fun a ↦ sphereChartDerivativeMap d p a (sphereWeakSolution d f)) (fun a i ↦ H a i)
    (sphereChartPrincipalDensity_smooth d p)
    (fun a ↦ (Lp.memLp _).mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun a i ↦ Lp.memLp (H a i))
    (fun a i psi hp hc hs ↦ (hw a i psi hp hc hs).2.2) k j l
  refine ⟨hFK.2.1,hG,fun psi hp hc hs ↦ ?_⟩
  have h := heq k psi hp hc hs
  have hFtest := hFK.2.2 psi hp hc hs
  have hGtest (j : Fin 4) : IntegrableOn (fun x ↦
      Yau.realWeakGradientCommutator (sphereChartPrincipalDensity d p)
        (fun a ↦ sphereChartDerivativeMap d p a (sphereWeakSolution d f)) k j x*Yau.coordPartial psi x j)
        (Yau.realCenteredCube 4 (1/2)) :=
    (hG j j).1.integrable_mul (Yau.real_continuous_memLp_compact hK _
      (Yau.real_coordPartial_smooth psi hp j).continuous)
  refine ⟨fun a j ↦ (h.1 a j).1,hFtest.2.1,hGtest,?_⟩
  rw [h.2.2,hFtest.2.2,neg_neg]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Yau.realWeakGradientCommutator,Finset.sum_mul]
  exact (integral_finsetSum Finset.univ (fun a _ ↦ (h.1 a j).2)).symm

end
end Yau.Target

end OAI
