import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import OAI.Algebra.Finitistic.Encoding.QuadraticEncoding
import OAI.Algebra.Finitistic.Rectification.RectificationAcyclic

namespace OAI

namespace LittleFinitistic.RelationSequence
open CategoryTheory CategoryTheory.Limits
open QuadraticEncoding

variable {k : Type*} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The actual length-two relation subspace, all paths, and their quotient. -/
noncomputable def sequence : ShortComplex (ModuleCat k) where
  X₁ := ModuleCat.of k (relationSpace P)
  X₂ := ModuleCat.of k (Paths k d)
  X₃ := ModuleCat.of k (Paths k d ⧸ relationSpace P)
  f := ModuleCat.ofHom
    { toFun := fun x => x.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  g := ModuleCat.ofHom
    { toFun := (relationSpace P).mkQ
      map_add' := (relationSpace P).mkQ.map_add
      map_smul' := (relationSpace P).mkQ.map_smul }
  zero := by ext x; exact (Submodule.Quotient.mk_eq_zero _).2 x.property

/-- No additional relation appears: the path quotient sequence is genuinely exact. -/
theorem sequence_shortExact : (sequence P).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change (relationSpace P).mkQ x = 0 ↔ ∃ y : relationSpace P, (y : Paths k d) = x
    constructor
    · intro hx
      exact ⟨⟨x,(Submodule.Quotient.mk_eq_zero _).1 hx⟩,rfl⟩
    · rintro ⟨y,hy⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 (hy ▸ y.property)
  · exact (relationSpace P).injective_subtype
  · exact (relationSpace P).mkQ_surjective

/-- Over the base field this exact sequence has an actual splitting. -/
noncomputable def sequenceSplitting : (sequence P).Splitting :=
  (sequence_shortExact P).splittingOfProjective

/-- The finite relation basis used by the manuscript exists for this exact subspace. -/
noncomputable def relationBasis : Module.Basis (Fin (Module.finrank k (relationSpace P))) k
    (relationSpace P) := by
  letI : Module.Free k (relationSpace P) := Module.Free.of_divisionRing k (relationSpace P)
  exact Module.finBasis k (relationSpace P)

/-- Tensoring the split path sequence with a complex, or applying any additive
realization functor, gives a short exact sequence of actual complexes. -/
theorem realized_sequence_shortExact {C : Type*} [Category C] [Abelian C]
    (F : ModuleCat k ⥤ CochainComplex C ℤ) [F.Additive] :
    ((sequence P).map F).ShortExact :=
  ((sequenceSplitting P).map F).shortExact

/-- The (0,2) associated graded total is acyclic after such a realization. -/
theorem realized_sequence_total_acyclic {C : Type*} [Category C] [Abelian C]
    (F : ModuleCat k ⥤ CochainComplex C ℤ) [F.Additive] :
    (RectificationTotal.total ((sequence P).map F).g ((sequence P).map F).f
      (Homotopy.ofEq ((sequence P).map F).zero)).Acyclic :=
  RectificationAcyclic.short_exact_total_acyclic _ (realized_sequence_shortExact P F)
end LittleFinitistic.RelationSequence

end OAI
