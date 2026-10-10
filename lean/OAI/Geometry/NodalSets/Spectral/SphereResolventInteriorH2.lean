import OAI.Geometry.NodalSets.Charts.SphereInteriorGradientDifferenceBound
import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakDerivative

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_resolvent_interior_second_weak_derivatives (d : SphereEnergyData) (p : Base) :
    ∃ C1 > 0, ∀ f : SphereWeightedL2 d,
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))),
        (∑ a : Fin 4, ∑ i : Fin 4, ‖H a i‖^2) ≤ C1*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        ∀ (a i : Fin 4) (psi : Yau.Jets.Coord → ℝ),
          ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          IntegrableOn (fun x ↦ (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*
            Yau.coordPartial psi x i) (Yau.realCenteredCube 4 (1/2)) ∧
          IntegrableOn (fun x ↦ H a i x*psi x) (Yau.realCenteredCube 4 (1/2)) ∧
          (∫ x in Yau.realCenteredCube 4 (1/2),
            (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/2), H a i x*psi x) := by
  obtain ⟨C0,hC0,hb⟩ := sphere_resolvent_interior_gradient_difference_bound d p
  refine ⟨16*C0,by positivity,fun f ↦ ?_⟩
  let E : ℝ := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have h (a i : Fin 4) := Yau.real_interior_weak_derivative_of_difference_bound
    (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) (Lp.memLp _) i (C0*E)
    (mul_nonneg hC0.le hE) (fun h hh ↦ (hb f i h hh).1 a)
    (fun h hh ↦ (Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 4 ↦ ∫ x in Yau.realCenteredCube 4 (1/2),
        (Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j (sphereWeakSolution d f)) x)^2)
      (fun j _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) (Finset.mem_univ a)).trans (hb f i h hh).2)
  choose H hH hweak using h
  refine ⟨H,?_,hweak⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hH a i))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,
    ← mul_assoc,show (4:ℝ)*4=16 by norm_num] using hsum

end
end Yau.Target

end OAI
