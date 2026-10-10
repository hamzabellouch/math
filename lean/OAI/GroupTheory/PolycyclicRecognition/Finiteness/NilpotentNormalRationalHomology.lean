import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalRootCoreHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalCoefficientHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalNormalExtensionHomology

namespace OAI

/-! # Rational homology for a finite-rank nilpotent normal kernel

The rank premise is retained. The proof supplies finite rational dimensions
for the canonical derived quotient action and the actual extension homology;
it does not deduce rank from ambient FP-infinity.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]
variable [Countable N] [Group.IsNilpotent N]
variable [Module.Finite ℚ (RationalAbelianSpace (Abelianization N))]

theorem nilpotentNormal_rationalDerived_finite (i : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] normalDerivedHomology N i) := by
  let : Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology (trivialIntegral N) i) :=
    nilpotent_rational_homology_finite_of_abelianization (trivialIntegral N) i
  let e := ((normalDerivedHomologyIso N i).symm.toLinearEquiv).baseChange ℤ ℚ _ _
  exact Module.Finite.equiv e

theorem normalExtension_rational_secondPage_finite_of_kernel_rank
    (hQ : TypeFPInfinity (G ⧸ N)) (i j : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology (normalDerivedHomology N i) j) := by
  let := nilpotentNormal_rationalDerived_finite N i
  exact (hQ j).rational_homology_finite (normalDerivedHomology N i)

theorem normalExtension_rational_homology_finite_of_kernel_rank
    (hQ : TypeFPInfinity (G ⧸ N)) (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology (trivialIntegral G) n) := by
  apply normalExtension_rational_homology_finite_of_secondPage N n
  intro i j _
  exact normalExtension_rational_secondPage_finite_of_kernel_rank N hQ i j

end PolycyclicRecognition

end

end OAI
