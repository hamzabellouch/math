import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SmallCoefficientRing
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepCofiber

namespace OAI

/-! # Removing the constant functions from the small coefficient ring

The constant copy of the integers is a subrepresentation. Its quotient is
again projective over the integers: evaluation at the identity splits the
underlying sequence. The splitting is not asserted to be equivariant.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G]

def smallCoefficientConstant : ℤ →ₗ[ℤ] SmallCoefficientRing G where
  toFun z := ⟨fun _ => z, ∅, fun _ _ _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def smallCoefficientEvaluation : SmallCoefficientRing G →ₗ[ℤ] ℤ where
  toFun f := f.val 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem smallCoefficientEvaluation_constant (z : ℤ) :
    smallCoefficientEvaluation G (smallCoefficientConstant G z) = z := rfl

def smallCoefficientUnit : trivialIntegral G ⟶ smallCoefficientRepresentation G :=
  Rep.ofHom ⟨smallCoefficientConstant G, fun _ => by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    funext x
    rfl⟩

def smallCoefficientConstants : Submodule ℤ (SmallCoefficientRing G) :=
  LinearMap.range (smallCoefficientConstant G)

theorem smallCoefficientConstants_invariant (g : G) :
    smallCoefficientConstants G ≤
      (smallCoefficientConstants G).comap ((smallCoefficientRepresentation G).ρ g) := by
  rintro _ ⟨z, rfl⟩
  exact ⟨z, rfl⟩

abbrev smallCoefficientQuotient : Rep ℤ G :=
  Rep.quotient (smallCoefficientRepresentation G) (smallCoefficientConstants G)
    (smallCoefficientConstants_invariant G)

def smallCoefficientQuotientMap : smallCoefficientRepresentation G ⟶ smallCoefficientQuotient G :=
  Rep.mkQ (smallCoefficientRepresentation G) (smallCoefficientConstants G)
    (smallCoefficientConstants_invariant G)

def smallCoefficientReduction : SmallCoefficientRing G →ₗ[ℤ] SmallCoefficientRing G :=
  LinearMap.id - (smallCoefficientConstant G).comp (smallCoefficientEvaluation G)

theorem smallCoefficientReduction_constant (z : ℤ) :
    smallCoefficientReduction G (smallCoefficientConstant G z) = 0 := by
  change smallCoefficientConstant G z - smallCoefficientConstant G z = 0
  exact sub_self _

/-- An integer-linear section of the quotient by the constant functions. -/
def smallCoefficientQuotientSection :
    smallCoefficientQuotient G →ₗ[ℤ] SmallCoefficientRing G :=
  (smallCoefficientConstants G).liftQ (smallCoefficientReduction G) (by
    rintro _ ⟨z, rfl⟩
    exact smallCoefficientReduction_constant G z)

theorem smallCoefficientQuotient_section :
    (smallCoefficientConstants G).mkQ.comp (smallCoefficientQuotientSection G) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change (smallCoefficientConstants G).mkQ
      (x - smallCoefficientConstant G (smallCoefficientEvaluation G x)) =
        (smallCoefficientConstants G).mkQ x
    rw [map_sub]
    have hz : (smallCoefficientConstants G).mkQ
        (smallCoefficientConstant G (smallCoefficientEvaluation G x)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
    rw [hz, sub_zero]

theorem smallCoefficientQuotient_integer_projective [Countable G] :
    Module.Projective ℤ (smallCoefficientQuotient G) :=
  Module.Projective.of_split (smallCoefficientQuotientSection G)
    (smallCoefficientConstants G).mkQ (smallCoefficientQuotient_section G)

theorem smallCoefficientUnit_quotient :
    smallCoefficientUnit G ≫ smallCoefficientQuotientMap G = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩

def smallCoefficientSequence : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (smallCoefficientUnit G) (smallCoefficientQuotientMap G)
    (smallCoefficientUnit_quotient G)

theorem smallCoefficientSequence_shortExact : (smallCoefficientSequence G).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (rep_shortComplex_exact_iff _).mpr
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero _).mp hx
  · apply (Rep.mono_iff_injective _).mpr
    intro z w h
    exact congrArg (smallCoefficientEvaluation G) h
  · apply (Rep.epi_iff_surjective _).mpr
    exact (smallCoefficientConstants G).mkQ_surjective

end PolycyclicRecognition

end

end OAI
