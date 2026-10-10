import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import Mathlib.CategoryTheory.SmallObject.Basic

namespace OAI

section

/-!
# The actual Kan--Quillen input and the Thomason lifting classes

The weak equivalences are those of geometric realizations, cofibrations are
monomorphisms, and fibrations lift against Mathlib's explicit horn inclusions.
The classical input is exactly the two weak factorization systems and the
two-out-of-three property from Goerss--Jardine (1999), Theorems I.11.3–I.11.4 and Corollary II.8.6.
There is no assumption of a model structure on strict higher categories.
-/

namespace Thomason.Construction

open CategoryTheory HomotopicalAlgebra
open SSet.modelCategoryQuillen

universe u

/-- The portion of the published Kan--Quillen theorem required by transfer,
with all three classes fixed to their actual definitions. -/
structure KanQuillenPublishedInput : Prop where
  twoOutOfThree : realizationWeakEquivalences.{u}.HasTwoOutOfThreeProperty
  cofibrationFactorization : MorphismProperty.IsWeakFactorizationSystem
    (MorphismProperty.monomorphisms SSet.{u})
    (J.rlp ⊓ realizationWeakEquivalences.{u})
  fibrationFactorization : MorphismProperty.IsWeakFactorizationSystem
    (MorphismProperty.monomorphisms SSet.{u} ⊓ realizationWeakEquivalences.{u}) J.rlp

namespace KanQuillenPublishedInput

variable (kq : KanQuillenPublishedInput.{u})

/-- The classical input constructs Mathlib's full model-category interface.
The weak-equivalence class is defined by geometric realization. -/
@[instance_reducible]
noncomputable def model : ModelCategory SSet.{u} := by
  letI : CategoryWithWeakEquivalences SSet.{u} := ⟨realizationWeakEquivalences⟩
  letI : (weakEquivalences SSet.{u}).HasTwoOutOfThreeProperty := kq.twoOutOfThree
  letI : MorphismProperty.IsWeakFactorizationSystem
      (cofibrations SSet.{u}) (trivialFibrations SSet.{u}) := kq.cofibrationFactorization
  letI : MorphismProperty.IsWeakFactorizationSystem
      (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) := kq.fibrationFactorization
  exact ModelCategory.mk' SSet.{u}

include kq

/-- Boundary lifting detects precisely the trivial Kan fibrations. This
uses Mathlib's proved generation of monomorphisms by boundary inclusions. -/
theorem trivialFibrations_eq_boundary_rlp :
    J.rlp ⊓ realizationWeakEquivalences.{u} = I.rlp := by
  have := kq.cofibrationFactorization
  exact (MorphismProperty.rlp_eq_of_wfs
    (MorphismProperty.monomorphisms SSet.{u}) _).symm.trans SSet.rlp_monomorphisms

end KanQuillenPublishedInput

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities)

/-- The right adjoint candidate Ex² N on the actual strict category. -/
noncomputable def thomasonRight : StrictOmegaCategory.{0} ⥤ SSet.{0} :=
  h.streetNerve ⋙ SSet.ex ⋙ SSet.ex

/-- The prescribed fibrations are detected by actual horn lifting. -/
noncomputable def thomasonFibrations : MorphismProperty StrictOmegaCategory.{0} :=
  J.rlp.inverseImage h.thomasonRight

/-- The prescribed cofibrations, using the lifting definition of the paper. -/
noncomputable def thomasonCofibrations : MorphismProperty StrictOmegaCategory.{0} :=
  (h.thomasonFibrations ⊓ h.streetWeakEquivalences).llp

/-- The prescribed trivial fibrations are exactly the maps whose twice
extended Street nerve lifts against all boundary inclusions. This is the
compatibility needed to apply the transfer theorem's generating cofibrations. -/
theorem thomason_trivialFibrations_eq_boundary_lifting
    (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X, realizationWeakEquivalences.{0} (canonicalExtension.app X)) :
    h.thomasonFibrations ⊓ h.streetWeakEquivalences =
      I.rlp.inverseImage h.thomasonRight := by
  have := kq.twoOutOfThree
  apply MorphismProperty.ext
  intro C D f
  change (J.rlp (h.thomasonRight.map f) ∧
    realizationWeakEquivalences (h.streetNerve.map f)) ↔ I.rlp (h.thomasonRight.map f)
  rw [← kq.trivialFibrations_eq_boundary_rlp]
  change (_ ∧ _) ↔ (_ ∧ realizationWeakEquivalences (h.thomasonRight.map f))
  apply and_congr Iff.rfl
  exact (realization_ex_twice_iff hj (h.streetNerve.map f)).symm

end NormalizedSimplexIdentities
end Thomason.Construction

end

section

/-! # The published simplicial gluing input

Goerss--Jardine, *Simplicial Homotopy Theory* (1999), Lemma II.8.8,
pp.127--128 (and Lemma II.8.12), applied to simplicial sets: in a map
of pushout squares, one specified leg in each square is a monomorphism.
Three weak equivalences induce a weak equivalence on pushouts. The class
below is the actual geometric-realization weak-equivalence class.

Source:
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Goerss-Jardine2.pdf
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

/-- Only the simplicial specialization of the classical gluing lemma. -/
structure PublishedSimplicialGluingInput : Prop where
  glue {A B C P A' B' C' P' : SSet.{0}}
    {i : A ⟶ B} {j : A ⟶ C} {b : B ⟶ P} {c : C ⟶ P}
    {i' : A' ⟶ B'} {j' : A' ⟶ C'} {b' : B' ⟶ P'} {c' : C' ⟶ P'}
    (hp : IsPushout i j b c) (hp' : IsPushout i' j' b' c')
    [Mono i] [Mono i']
    (fA : A ⟶ A') (fB : B ⟶ B') (fC : C ⟶ C') (fP : P ⟶ P')
    (hi : i ≫ fB = fA ≫ i') (hj : j ≫ fC = fA ≫ j')
    (hb : b ≫ fP = fB ≫ b') (hc : c ≫ fP = fC ≫ c')
    (hA : realizationWeakEquivalences fA) (hB : realizationWeakEquivalences fB)
    (hC : realizationWeakEquivalences fC) : realizationWeakEquivalences fP

namespace PublishedSimplicialGluingInput

variable (g : PublishedSimplicialGluingInput)

include g

/-- A common source mapping weakly equivalently into both pieces and their
intersection maps weakly equivalently into their pushout. -/
theorem common_source {A B C P X : SSet.{0}}
    {i : A ⟶ B} {j : A ⟶ C} {b : B ⟶ P} {c : C ⟶ P}
    (hp : IsPushout i j b c) [Mono i]
    (fA : X ⟶ A) (fB : X ⟶ B) (fC : X ⟶ C) (fP : X ⟶ P)
    (hi : fA ≫ i = fB) (hj : fA ≫ j = fC)
    (hb : fB ≫ b = fP) (hc : fC ≫ c = fP)
    (hA : realizationWeakEquivalences fA) (hB : realizationWeakEquivalences fB)
    (hC : realizationWeakEquivalences fC) : realizationWeakEquivalences fP := by
  have htop : IsPushout (𝟙 X) (𝟙 X) (𝟙 X) (𝟙 X) := IsPushout.of_id_fst
  exact g.glue htop hp fA fB fC fP
    (by simpa using hi.symm) (by simpa using hj.symm)
    (by simpa using hb.symm) (by simpa using hc.symm) hA hB hC

end PublishedSimplicialGluingInput
end Thomason.Construction

end

section

/-! # Small generating families in a locally presentable category

One regular cardinal bounds the presentability ranks of a small family of
domains. This supplies precisely the colimit preservation used by the
small object argument, without requiring finite presentability.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

universe u

variable {C : Type u} [Category.{0} C] [IsLocallyPresentable.{0} C]
    {ι : Type} {A B : ι → C}

/-- Any small family of actual maps permits the small object argument. -/
theorem smallFamily_hasSmallObjectArgument (f : ∀ i, A i ⟶ B i) :
    (MorphismProperty.ofHoms f).HasSmallObjectArgument.{0} := by
  have : HasColimitsOfSize.{0,0} C := by
    obtain ⟨κ, _, hC⟩ := IsLocallyPresentable.exists_cardinal.{0} C
    exact hC.toHasColimitsOfSize
  obtain ⟨κ, hκ, hA⟩ :=
    ObjectProperty.le_isCardinalPresentable.{0} (ObjectProperty.ofObj A)
  let : Fact κ.IsRegular := hκ
  have : Nonempty κ.ord.ToType := by simpa using hκ.out.ne_zero
  let := WellFoundedLT.toOrderBot κ.ord.ToType
  refine ⟨κ, inferInstance, inferInstance, ?_⟩
  refine { preservesColimit := ?_ }
  rintro _ _ _ _ _ ⟨j⟩ _g hg
  have : IsCardinalPresentable (A j) κ := hA _ (ObjectProperty.ofObj_apply A j)
  let := (coyoneda.obj (Opposite.op (A j))).preservesColimitsOfShape_of_isCardinalAccessible
    κ κ.ord.ToType
  exact (inferInstance : PreservesColimit hg.F (coyoneda.obj (Opposite.op (A j))))

/-- The lifting classes of a small family form the actual weak
factorization system given by the small object argument. -/
theorem smallFamily_weakFactorizationSystem (f : ∀ i, A i ⟶ B i) :
    MorphismProperty.IsWeakFactorizationSystem
      (MorphismProperty.ofHoms f).rlp.llp (MorphismProperty.ofHoms f).rlp := by
  let := smallFamily_hasSmallObjectArgument f
  exact { rlp := (MorphismProperty.ofHoms f).rlp_llp_rlp, llp := rfl }

end Thomason.Construction

end

section

/-! # The acyclicity criterion for recognition

The horn weak factorization system identifies its left class with weak
cofibrations as soon as its left maps are known to be weak equivalences.
The proof is the explicit retract argument, using two-out-of-three.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.MorphismProperty

universe v u

variable {C : Type u} [Category.{v} C] (W F : MorphismProperty C)
    [W.HasTwoOutOfThreeProperty] [IsWeakFactorizationSystem F.llp F]

theorem leftLifting_eq_cofibration_inter_weak (h : F.llp ≤ W) :
    F.llp = (F ⊓ W).llp ⊓ W := by
  apply le_antisymm
  · intro X Y f hf
    exact ⟨antitone_llp inf_le_left f hf, h f hf⟩
  · intro X Y f hf
    let d := factorizationData F.llp F f
    have hiw : W d.i := h d.i d.hi
    have hpw : W d.p := by
      apply W.of_precomp d.i d.p hiw
      simpa only [d.fac] using hf.2
    let : HasLiftingProperty f d.p := hf.1 d.p ⟨d.hp, hpw⟩
    let sq : CommSq d.i f d.p (𝟙 Y) := ⟨d.fac.trans (Category.comp_id f).symm⟩
    let r : RetractArrow f d.i := {
      i := Arrow.homMk (𝟙 X) sq.lift ((Category.id_comp d.i).trans sq.fac_left.symm)
      r := Arrow.homMk (𝟙 X) d.p ((Category.id_comp f).trans d.fac.symm)
      retract := by
        apply Arrow.hom_ext
        · simp
        · exact sq.fac_right }
    exact F.llp.of_retract r d.hi

theorem weakCofibration_factorization_of_leftLifting_weak (h : F.llp ≤ W) :
    IsWeakFactorizationSystem ((F ⊓ W).llp ⊓ W) F := by
  rw [← leftLifting_eq_cofibration_inter_weak W F h]
  infer_instance

end Thomason.Construction

end

end OAI
