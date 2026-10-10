import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalNilpotentHomologyVanishing
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalZeroCoefficientHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalNormalExtensionHomology

namespace OAI

/-! # A rational homology bound for a finite-rank nilpotent extension

The bound is obtained from the actual normal-extension bicomplex. Its kernel
rank hypothesis is explicit, and kernel torsion is permitted.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem normalExtension_rational_homology_isZero_of_kernel_bound (a b : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral (G ⧸ N)) b]
    (hN : ∀ i : ℕ, a < i →
      IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology (trivialIntegral N) i)))
    (n : ℕ) (hn : a + b < n) :
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology (trivialIntegral G) n)) := by
  apply normalExtension_rational_homology_isZero_above N a b ?_ n hn
  intro i j hij
  rcases hij with hi | hj
  · have hz : IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] normalDerivedHomology N i)) :=
      (hN i hi).of_iso (rationalModuleFunctor.mapIso (normalDerivedHomologyIso N i))
    exact rational_groupHomology_isZero_of_coefficient (normalDerivedHomology N i) hz j
  · exact rationalModuleFunctor.map_isZero
      (groupHomology_isZero_above_dimension b (normalDerivedHomology N i) j hj)

theorem nilpotentNormal_rational_homology_bounded
    [Countable N] [Group.IsNilpotent N]
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization N))]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N)) :
    ∃ d : ℕ, ∀ n : ℕ, d < n →
      IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology (trivialIntegral G) n)) := by
  obtain ⟨a, ha⟩ := nilpotent_rational_homology_bounded_of_abelianization (G := N)
  obtain ⟨b, hb⟩ := hQ
  let := hb
  exact ⟨a + b, normalExtension_rational_homology_isZero_of_kernel_bound N a b
    (ha (trivialIntegral N))⟩

theorem torsionNilpotentNormal_rational_homology_isZero
    [Countable N] [Group.IsNilpotent N] (ht : ∀ g : N, IsOfFinOrder g)
    (b : ℕ) [HasProjectiveDimensionLE (trivialIntegral (G ⧸ N)) b]
    (n : ℕ) (hn : b < n) :
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology (trivialIntegral G) n)) := by
  exact normalExtension_rational_homology_isZero_of_kernel_bound N 0 b
    (fun i hi => torsion_nilpotent_rational_homology_isZero ht (trivialIntegral N) i hi)
    n (by simpa using hn)

end PolycyclicRecognition

end

end OAI
