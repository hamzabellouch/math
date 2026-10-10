import OAI.Geometry.NodalSets.Elliptic.RealNestedWeakDerivative
import OAI.Geometry.NodalSets.Spectral.SphereEigenThirdDifferenceBound

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_eigen_interior_fourth_weak_derivatives (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) :
    ∃ C2 > 0, ∃ C3 > 0, ∃ C4 > 0, ∀ (f : SphereWeightedL2 d), sphereL2Resolvent d f=mu • f →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))),
      ∃ J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))),
      ∃ L : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/8))),
        (∑ a, ∑ k, ‖H a k‖^2) ≤ C2*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          (∫ x in Yau.realCenteredCube 4 (1/2),
            (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x k) =
            -(∫ x in Yau.realCenteredCube 4 (1/2), H a k x*psi x)) ∧
        (∑ a, ∑ k, ∑ i, ‖J a k i‖^2) ≤ C3*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
          IntegrableOn (fun x ↦ H a k x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 (1/4)) ∧
          IntegrableOn (fun x ↦ J a k i x*psi x) (Yau.realCenteredCube 4 (1/4)) ∧
          (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/4), J a k i x*psi x)) ∧
        (∑ a, ∑ k, ∑ l, ∑ i, ‖L a k l i‖^2) ≤ C4*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        ∀ a k l i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/8) →
          IntegrableOn (fun x ↦ J a k l x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 (1/8)) ∧
          IntegrableOn (fun x ↦ L a k l i x*psi x) (Yau.realCenteredCube 4 (1/8)) ∧
          (∫ x in Yau.realCenteredCube 4 (1/8), J a k l x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/8), L a k l i x*psi x) := by
  obtain ⟨C2,hC2,C3,hC3,hall⟩ := sphere_eigen_interior_third_weak_derivatives d p hrho mu hmu
  obtain ⟨C,hC,hbound⟩ := sphere_same_third_difference_bound d p hrho mu hmu C2 C3 hC2.le hC3.le
  refine ⟨C2,hC2,C3,hC3,256*C,by positivity,fun f heigen ↦ ?_⟩
  obtain ⟨H,J,hH,hsecond,hJ,hthird⟩ := hall f heigen
  have hdiff := hbound f heigen H J hsecond
    (fun a k l psi hp hc hs ↦ (hthird a k l psi hp hc hs).2.2) hH hJ
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hder (a k l i : Fin 4) :
      ∃ L : Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/8))), ‖L‖^2 ≤ C*E ∧
        ∀ psi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/8) →
          IntegrableOn (fun x ↦ J a k l x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 (1/8)) ∧
          IntegrableOn (fun x ↦ L x*psi x) (Yau.realCenteredCube 4 (1/8)) ∧
          (∫ x in Yau.realCenteredCube 4 (1/8), J a k l x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/8), L x*psi x) := by
    apply Yau.real_nested_weak_derivative_of_difference_bound (1/4) (1/8) (1/64)
      (by norm_num) (by norm_num) (by norm_num) (J a k l) (Lp.memLp _) i (C*E) (mul_nonneg hC.le hE)
      (fun h hh ↦ (hdiff a k i h hh).1 l)
    intro h hh
    exact (Finset.single_le_sum (f := fun b ↦ ∫ x in Yau.realCenteredCube 4 (1/8),
      (Yau.realDifferenceQuotient i h (J a k b) x)^2)
      (fun b _ ↦ integral_nonneg (fun x ↦ sq_nonneg _)) (Finset.mem_univ l)).trans (hdiff a k i h hh).2
  choose L hL hpair using hder
  refine ⟨H,J,L,hH,hsecond,hJ,hthird,?_,hpair⟩
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦
      Finset.sum_le_sum (s := Finset.univ) (fun l _ ↦
        Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hL a k l i))))
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at ht
  exact ht.trans_eq (by ring)

end
end Yau.Target

end OAI
