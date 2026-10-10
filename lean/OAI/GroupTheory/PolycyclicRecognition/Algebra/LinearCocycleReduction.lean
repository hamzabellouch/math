import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemCocycleReduction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionConjugation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentLangMap

namespace OAI

/-! # Removing a moving cocycle component by an explicit Lang correction -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {N K Q : Type} [Group N] [Group Q] [IsMulCommutative Q]
  [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [P : PolynomialExponentialCoordinates K] [LieRing.IsNilpotent K]

theorem factorSystem_cocycle_reduction_of_fixedPointFree_action
    (S : NonabelianFactorSystem N Q) (R : NonabelianFactorSystem K Q)
    (p : N →* K) (j : K →* N) (hpj : ∀ x, p (j x) = x)
    (hact : ∀ q x, p (S.action q x) = R.action q (p x))
    (hfactor : ∀ q r, p (S.factor q r) = R.factor q r)
    (q₀ : Q) (A : K ≃ₗ⁅ℝ⁆ K) (hA : ∀ x, R.action q₀ x = A x)
    (hbij : Function.Bijective (fun x : K => A x - x)) :
    ∃ b : Q → N, ∃ hb : b 1 = 1, ∀ q r, p ((S.gauge b hb).factor q r) = 1 := by
  let E := FactorExtension.groupExtension R
  let t : FactorExtension R := ⟨1, q₀⟩
  have heq : extensionLangMap E t = fun x : K => x⁻¹ * A x := by
    funext x
    change x⁻¹ * E.conjAct t x = x⁻¹ * A x
    rw [FactorExtension.conjugation_section, hA]
  have hlang : Function.Bijective (extensionLangMap E t) := by
    rw [heq]
    exact polynomial_lang_bijective A hbij
  let s := centralizerSplitting E t (fun q => Commute.all _ q) hlang
  exact factorSystem_cocycle_reduction S R p j hpj hact hfactor s

end PolycyclicRecognition

end

end OAI
