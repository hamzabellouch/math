import OAI.GroupTheory.PolycyclicRecognition.Analysis.ElementaryAmenable
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Ext

namespace OAI

/-!
# The finiteness and duality properties used in recognition

These are concrete properties of the trivial integral representation and its
projective resolutions. A finite classifying space supplies a finite resolution
of this kind, but no predicate for an unspecified classifying space is used.
The cohomology condition includes the possibly nontrivial orientation action:
only the underlying integral module in top degree is required to be `ℤ`.
-/

namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra

variable (G : Type) [Group G]

/-- The trivial integral representation used to compute integral finiteness. -/
abbrev trivialIntegral : Rep ℤ G := Rep.trivial ℤ G ℤ

/-- Finite generation refers to the group-ring action of the representation. -/
def IntegralRepresentationFinite (A : Rep ℤ G) : Prop :=
  letI : Module ℤ A := A.hV2
  Module.Finite ℤ[G] A.ρ.asModule

/-- Type `FP_n(ℤ)`: a projective resolution finite over `ℤ[G]` through degree `n`. -/
def TypeFP (n : ℕ) : Prop :=
  ∃ P : ProjectiveResolution (trivialIntegral G),
    ∀ i, i ≤ n → IntegralRepresentationFinite G (P.complex.X i)

/-- Type `FP_∞(ℤ)` means type `FP_n(ℤ)` in every finite degree. -/
def TypeFPInfinity : Prop := ∀ n, TypeFP G n

/-- A finite projective resolution, with all terms finite over the group ring. -/
def HasFiniteProjectiveResolution : Prop :=
  ∃ (P : ProjectiveResolution (trivialIntegral G)) (d : ℕ),
    (∀ i, IntegralRepresentationFinite G (P.complex.X i)) ∧
    ∀ i, d < i → IsZero (P.complex.X i)

/-- Finite integral cohomological dimension is finite projective dimension of
the trivial integral representation. -/
def HasFiniteIntegralCohomologicalDimension : Prop :=
  ∃ d : ℕ, HasProjectiveDimensionLE (trivialIntegral G) d

/-- Integral Poincaré duality in dimension `n`, allowing an orientation twist. -/
def IsIntegralPoincareDualityGroup (n : ℕ) : Prop :=
  HasFiniteProjectiveResolution G ∧
  (∀ i, i ≠ n → IsZero (groupCohomology (Rep.leftRegular ℤ G) i)) ∧
  Nonempty (groupCohomology (Rep.leftRegular ℤ G) n ≅ ModuleCat.of ℤ ℤ)

theorem HasFiniteProjectiveResolution.typeFPInfinity
    (h : HasFiniteProjectiveResolution G) : TypeFPInfinity G := by
  obtain ⟨P, d, hfg, _⟩ := h
  exact fun n => ⟨P, fun i _ => hfg i⟩

theorem IsIntegralPoincareDualityGroup.typeFPInfinity {n : ℕ}
    (h : IsIntegralPoincareDualityGroup G n) : TypeFPInfinity G :=
  h.1.typeFPInfinity G

/-- The bounded resolution in the definition really implies finite
cohomological dimension: every higher Ext cocycle has zero source. -/
theorem HasFiniteProjectiveResolution.finiteCohomologicalDimension
    (h : HasFiniteProjectiveResolution G) :
    HasFiniteIntegralCohomologicalDimension G := by
  obtain ⟨P, d, _, hz⟩ := h
  let := HasExt.standard (Rep ℤ G)
  refine ⟨d, HasProjectiveDimensionLT.mk ?_⟩
  intro i hi Y e
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (i + 1) rfl
  have hzero : f = 0 := (hz i (Nat.lt_of_succ_le hi)).eq_of_src f 0
  subst f
  exact P.extMk_zero (i + 1) rfl

theorem IsIntegralPoincareDualityGroup.finiteCohomologicalDimension {n : ℕ}
    (h : IsIntegralPoincareDualityGroup G n) :
    HasFiniteIntegralCohomologicalDimension G :=
  h.1.finiteCohomologicalDimension G

end PolycyclicRecognition

end OAI
