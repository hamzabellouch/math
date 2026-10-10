import OAI.GroupTheory.PolycyclicRecognition.Algebra.InnerCentralizerFactorSystem
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleCocycleReductionPreserving

namespace OAI

/-! # Central cocycle corrections in ambient exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group Q] [IsMulCommutative Q]

theorem ambient_semisimple_cocycle_reduction (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (S : L ≃ₗ⁅ℝ⁆ L) (hS : Module.End.IsSemisimple S.toLinearMap)
    (hSA : ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (q₀ : Q) (U : L ≃ₗ⁅ℝ⁆ L) (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : (A q₀).toLinearMap = S.toLinearMap * U.toLinearMap) :
    ∃ b : Q → L, ∃ hb : b 1 = 1,
      (∀ q, b q ∈ Subgroup.center L) ∧
      (∀ q x, (F.gauge b hb).action q x = F.action q x) ∧
      (∀ q r, S ((F.gauge b hb).factor q r) = (F.gauge b hb).factor q r) ∧
      ∀ T : L ≃ₗ⁅ℝ⁆ L, Commute S.toLinearMap T.toLinearMap →
        (∀ q, Commute T.toLinearMap (A q).toLinearMap) →
        (∀ q r, T (F.factor q r) = F.factor q r) → ∀ q, T (b q) = b q := by
  let R := innerCentralizerFactorSystem F A hact S hSA
  obtain ⟨c, hc, hcZ, hcS, hcT⟩ := semisimple_cocycle_reduction_preserving S hS R A hSA
    (fun _ _ => rfl) q₀ U hU hSU hA
  let b : Q → L := fun q => c q
  have hb : b 1 = 1 := congrArg Subtype.val hc
  have hZ : ∀ q, b q ∈ Subgroup.center L := fun q =>
    polynomial_mem_center_of_lie_eq_zero _ (fun y => LinearMap.congr_fun (hcZ q) y)
  refine ⟨b, hb, hZ, ?_, ?_, ?_⟩
  · intro q x
    change b q * F.action q x * (b q)⁻¹ = F.action q x
    rw [← Subgroup.mem_center_iff.mp (hZ q) (F.action q x)]
    group
  · intro q r
    have he : ((R.gauge c hc).factor q r : L) = (F.gauge b hb).factor q r := by
      change b q * A q (b r) * F.factor q r * (b (q * r))⁻¹ =
        b q * F.action q (b r) * F.factor q r * (b (q * r))⁻¹
      rw [hact]
    rw [← he]
    exact hcS q r
  · intro T hST hTA hTF q
    exact hcT T hST hTA hTF q

end PolycyclicRecognition

end

end OAI
