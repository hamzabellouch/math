import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CoefficientNormalHomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalNilpotentRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentTorsionSubgroup

namespace OAI

/-! # Uniform rational bounds through locally finite kernels

The comparison holds for arbitrary coefficient representations and therefore
transports a uniform homology bound in both directions. For nilpotent groups
it relates finite rational rank to the torsion-free quotient's dimension.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [Countable N]

def locallyFiniteKernelCoefficientHomologyIso
    (hN : ∀ H : Subgroup N, H.FG → Finite H) (A : Rep.{0} ℤ G) (n : ℕ) :
    rationalModuleFunctor.obj (groupHomology A n) ≅
      rationalModuleFunctor.obj (groupHomology (A.quotientToCoinvariants N) n) :=
  rationalAcyclicKernelCoefficientHomologyIso N A
    (fun i hi => locallyFinite_rational_homology_isZero hN (Rep.res N.subtype A) i hi) n

def locallyFiniteKernelInflationHomologyIso
    (hN : ∀ H : Subgroup N, H.FG → Finite H) (A : Rep.{0} ℤ (G ⧸ N)) (n : ℕ) :
    rationalModuleFunctor.obj (groupHomology (Rep.res (QuotientGroup.mk' N) A) n) ≅
      rationalModuleFunctor.obj (groupHomology A n) :=
  locallyFiniteKernelCoefficientHomologyIso N hN (Rep.res (QuotientGroup.mk' N) A) n ≪≫
    rationalModuleFunctor.mapIso
      ((groupHomology.functor ℤ (G ⧸ N) n).mapIso (normalCoinvariantsInflationIso N A))

theorem locallyFiniteKernel_rational_homology_bound_iff
    (hN : ∀ H : Subgroup N, H.FG → Finite H) (d : ℕ) :
    RationalHomologyDimensionLE G d ↔ RationalHomologyDimensionLE (G ⧸ N) d := by
  constructor
  · intro hG A i hi
    exact (hG (Rep.res (QuotientGroup.mk' N) A) i hi).of_iso
      (locallyFiniteKernelInflationHomologyIso N hN A i).symm
  · intro hQ A i hi
    exact (hQ (A.quotientToCoinvariants N) i hi).of_iso
      (locallyFiniteKernelCoefficientHomologyIso N hN A i)

omit [N.Normal] [Countable N] in
theorem rational_homology_bound_of_integral_dimension (d : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral G) d] : RationalHomologyDimensionLE G d :=
  fun A i hi => rationalModuleFunctor.map_isZero
    (groupHomology_isZero_above_dimension d A i hi)

omit [N.Normal] [Countable N] in
theorem rational_homology_bound_of_finiteIndex_dimension
    (H : Subgroup G) [H.FiniteIndex] (d : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral H) d] : RationalHomologyDimensionLE G d :=
  fun A i hi => rational_homology_isZero_of_finiteIndex H A i
    (rational_homology_bound_of_integral_dimension d (Rep.res H.subtype A) i hi)

variable [Group.IsNilpotent G] [Countable G]

theorem nilpotent_rational_homology_bounded_iff_torsionQuotient_finiteDimension :
    (∃ d : ℕ, RationalHomologyDimensionLE G d) ↔
      HasFiniteIntegralCohomologicalDimension (G ⧸ nilpotentTorsionSubgroup) := by
  constructor
  · rintro ⟨d, hd⟩
    let := nilpotent_rational_abelianization_finite_of_homology_bound hd
    exact nilpotentTorsionQuotient_finiteDimension_of_finite_abelianization
  · rintro ⟨d, hd⟩
    let := hd
    exact ⟨d, (locallyFiniteKernel_rational_homology_bound_iff nilpotentTorsionSubgroup
      nilpotentTorsionSubgroup_locallyFinite d).mpr
        (rational_homology_bound_of_integral_dimension d)⟩

end PolycyclicRecognition

end

end OAI
