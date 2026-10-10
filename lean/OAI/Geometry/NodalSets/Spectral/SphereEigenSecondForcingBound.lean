import OAI.Geometry.NodalSets.Charts.SphereInteriorJetBound
import OAI.Geometry.NodalSets.Elliptic.RealFinitePositiveBounds
import OAI.Geometry.NodalSets.Elliptic.RealSecondCommutatorBound
import OAI.Geometry.NodalSets.Elliptic.RealSecondScalarBound

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_same_second_forcing_bound (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu C2 C3 : ℝ) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) :
    ∃ M > 0, ∀ (f : SphereWeightedL2 d)
      (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
      (J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4)))),
      (∑ a, ∑ k, ‖H a k‖^2) ≤ C2*(‖f‖^2+‖sphereWeakSolution d f‖^2) →
      (∑ a, ∑ k, ∑ i, ‖J a k i‖^2) ≤ C3*(‖f‖^2+‖sphereWeakSolution d f‖^2) →
      let Q := Yau.realCenteredCube 4 (1/4)
      let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
      let C := sphereChartPrincipalDensity d p
      let B := sphereEigenForcingCoefficient d p mu
      let w := fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)
      let U := fun a ↦ (sphereChartDerivativeMap d p a (sphereWeakSolution d f) : Yau.Jets.Coord → ℝ)
      ∀ k l j i,
        (MemLp (Yau.realSecondScalarForcing B w U (fun a b ↦ H a b) k l) 2 (volume.restrict Q) ∧
          (∫ x in Q, (Yau.realSecondScalarForcing B w U (fun a b ↦ H a b) k l x)^2) ≤ M*E) ∧
        (MemLp (Yau.realSecondCommutator C U (fun a b ↦ H a b) k l j) 2 (volume.restrict Q) ∧
          (∫ x in Q, (Yau.realSecondCommutator C U (fun a b ↦ H a b) k l j x)^2) ≤ M*E) ∧
        (MemLp (Yau.realSecondCommutatorDerivative C U (fun a b ↦ H a b)
            (fun a b c ↦ J a b c) k l j i) 2 (volume.restrict Q) ∧
          (∫ x in Q, (Yau.realSecondCommutatorDerivative C U (fun a b ↦ H a b)
            (fun a b c ↦ J a b c) k l j i x)^2) ≤ M*E) := by
  let Q := Yau.realCenteredCube 4 (1/4)
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/4)
  let B := sphereEigenForcingCoefficient d p mu
  have hB : ContDiff ℝ ∞ B := contDiff_const.mul (roundCoordDensity_smooth.mul hrho)
  obtain ⟨A,hA,hjet⟩ := sphere_same_interior_jet_bound d p C2 C3 hC2 hC3
  choose CF hCF hFb using fun k l ↦ Yau.real_second_scalar_forcing_bound hQ B hB k l
  obtain ⟨F0,hF0,hFmax⟩ := Yau.real_finite_positive_majorant (fun t : Fin 4 × Fin 4 ↦ CF t.1 t.2)
  choose CG hCG hGb using fun k l j ↦ Yau.real_second_commutator_bound hQ
    (sphereChartPrincipalDensity d p) (sphereChartPrincipalDensity_smooth d p) k l j
  obtain ⟨G0,hG0,hGmax⟩ := Yau.real_finite_positive_majorant
    (fun t : Fin 4 × Fin 4 × Fin 4 ↦ CG t.1 t.2.1 t.2.2)
  choose CD hCD hDb using fun k l j i ↦ Yau.real_second_commutator_derivative_bound hQ
    (sphereChartPrincipalDensity d p) (sphereChartPrincipalDensity_smooth d p) k l j i
  obtain ⟨D0,hD0,hDmax⟩ := Yau.real_finite_positive_majorant
    (fun t : Fin 4 × Fin 4 × Fin 4 × Fin 4 ↦ CD t.1 t.2.1 t.2.2.1 t.2.2.2)
  let M := (F0+G0+D0)*A
  refine ⟨M,by dsimp [M]; positivity,fun f H J hH hJ ↦ ?_⟩
  dsimp only
  intro k l j i
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hAE : 0 ≤ A*E := mul_nonneg hA.le hE
  obtain ⟨hw,hU,hH0,hJ0⟩ := hjet f H J hH hJ
  have hF := hFb k l _ _ _ hw.1 (fun a ↦ (hU a).1) (fun a b ↦ (hH0 a b).1)
    (A*E) hAE hw.2 (fun a ↦ (hU a).2) (fun a b ↦ (hH0 a b).2)
  have hG := hGb k l j _ _ (fun a ↦ (hU a).1) (fun a b ↦ (hH0 a b).1)
    (A*E) hAE (fun a ↦ (hU a).2) (fun a b ↦ (hH0 a b).2)
  have hD := hDb k l j i _ _ _ (fun a ↦ (hU a).1) (fun a b ↦ (hH0 a b).1)
    (fun a b c ↦ (hJ0 a b c).1) (A*E) hAE (fun a ↦ (hU a).2)
    (fun a b ↦ (hH0 a b).2) (fun a b c ↦ (hJ0 a b c).2)
  refine ⟨⟨hF.1,hF.2.trans ?_⟩,⟨hG.1,hG.2.trans ?_⟩,⟨hD.1,hD.2.trans ?_⟩⟩
  · have hm : CF k l ≤ F0+G0+D0 := by linarith [hFmax (k,l)]
    simpa only [M,mul_assoc] using mul_le_mul_of_nonneg_right hm hAE
  · have hm : CG k l j ≤ F0+G0+D0 := by linarith [hGmax (k,l,j)]
    simpa only [M,mul_assoc] using mul_le_mul_of_nonneg_right hm hAE
  · have hm : CD k l j i ≤ F0+G0+D0 := by linarith [hDmax (k,l,j,i)]
    simpa only [M,mul_assoc] using mul_le_mul_of_nonneg_right hm hAE

end
end Yau.Target

end OAI
