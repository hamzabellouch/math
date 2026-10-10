import OAI.Geometry.NodalSets.Elliptic.RealNestedWeakDerivative
import OAI.Geometry.NodalSets.Spectral.SphereEigenHessianDifferenceBound

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_eigen_interior_third_weak_derivatives (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) :
    ∃ C2 > 0, ∃ C3 > 0, ∀ (f : SphereWeightedL2 d), sphereL2Resolvent d f=mu • f →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))),
      ∃ J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))),
        (∑ a, ∑ k, ‖H a k‖^2) ≤ C2*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          (∫ x in Yau.realCenteredCube 4 (1/2),
            (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x k) =
            -(∫ x in Yau.realCenteredCube 4 (1/2), H a k x*psi x)) ∧
        (∑ a, ∑ k, ∑ i, ‖J a k i‖^2) ≤ C3*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        ∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
          IntegrableOn (fun x ↦ H a k x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 (1/4)) ∧
          IntegrableOn (fun x ↦ J a k i x*psi x) (Yau.realCenteredCube 4 (1/4)) ∧
          (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/4), J a k i x*psi x) := by
  obtain ⟨C2,hC2,C,hC,hall⟩ := sphere_eigen_hessian_difference_bound d p hrho mu hmu
  refine ⟨C2,hC2,64*C,by positivity,fun f heigen ↦ ?_⟩
  obtain ⟨H,hbound,hweak,hdiff⟩ := hall f heigen
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hder (a k i : Fin 4) :
      ∃ J : Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))), ‖J‖^2 ≤ C*E ∧
        ∀ psi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
          IntegrableOn (fun x ↦ H a k x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 (1/4)) ∧
          IntegrableOn (fun x ↦ J x*psi x) (Yau.realCenteredCube 4 (1/4)) ∧
          (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/4), J x*psi x) := by
    apply Yau.real_nested_weak_derivative_of_difference_bound (1/2) (1/4) (1/32)
      (by norm_num) (by norm_num) (by norm_num) (H a k) (Lp.memLp _) i (C*E) (mul_nonneg hC.le hE)
      (fun h hh ↦ (hdiff a i h hh).1 k)
    intro h hh
    exact (Finset.single_le_sum (f := fun l ↦ ∫ x in Yau.realCenteredCube 4 (1/4),
      (Yau.realDifferenceQuotient i h (H a l) x)^2)
      (fun l _ ↦ integral_nonneg (fun x ↦ sq_nonneg _)) (Finset.mem_univ k)).trans (hdiff a i h hh).2
  choose J hJ hpair using hder
  refine ⟨H,J,hbound,hweak,?_,hpair⟩
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦
      Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hJ a k i)))
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at ht
  have hscale : 4*(4*(4*(C*E)))=(64*C)*E := by ring
  exact ht.trans_eq hscale

end
end Yau.Target

end OAI
