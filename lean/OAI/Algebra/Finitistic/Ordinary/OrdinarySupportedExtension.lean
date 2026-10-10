import Mathlib.Algebra.Homology.Embedding.StupidTrunc

namespace OAI
noncomputable section
attribute [local instance] Classical.propDecidable
open CategoryTheory Limits
namespace LittleFinitistic.OrdinarySimulation.SupportedExtension
universe u v w w'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable {I : Type w} {J : Type w'} {c : ComplexShape I} {c' : ComplexShape J}
variable (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff] [K.IsStrictlySupported e]

/-- The supported complex's restriction and extension have its actual components. -/
def component (j : J) : (K.stupidTrunc e).X j ≅ K.X j :=
  if hj : ∃ i, e.f i = j then K.stupidTruncXIso e hj.choose_spec
  else (K.isZero_stupidTrunc_X e j (by simpa using hj)).iso
    (K.isZero_X_of_isStrictlySupported e j (by simpa using hj))

omit [K.IsStrictlySupported e] in
theorem component_iso_unique {i j : I} {n : J} (hi : e.f i = n) (hj : e.f j = n) :
    K.stupidTruncXIso e hi = K.stupidTruncXIso e hj := by
  have h : i = j := e.injective_f (hi.trans hj.symm)
  subst j
  rfl

theorem component_at (i : I) : component K e (e.f i) = K.stupidTruncXIso e rfl := by
  unfold component
  rw [dite_eq_left (show ∃ j, e.f j = e.f i from ⟨i,rfl⟩)]
  exact component_iso_unique K e _ _

/-- An actual chain isomorphism, with support supplied by proved zero objects. -/
def iso : K.stupidTrunc e ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (component K e) (by
    intro i' j' _
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i,rfl⟩ := hi
      by_cases hj : ∃ j, e.f j = j'
      · obtain ⟨j,rfl⟩ := hj
        rw [component_at,component_at]
        change (((K.restriction e).extendXIso e rfl).hom ≫ 𝟙 _) ≫ K.d (e.f i) (e.f j) =
          ((K.restriction e).extend e).d (e.f i) (e.f j) ≫
            (((K.restriction e).extendXIso e rfl).hom ≫ 𝟙 _)
        rw [Category.comp_id, Category.comp_id]
        rw [HomologicalComplex.extend_d_eq _ _ rfl rfl]
        simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
        rfl
      · exact IsZero.eq_of_tgt (K.isZero_X_of_isStrictlySupported e j' (by simpa using hj)) _ _
    · exact IsZero.eq_of_src (K.isZero_stupidTrunc_X e i' (by simpa using hi)) _ _)
end LittleFinitistic.OrdinarySimulation.SupportedExtension

end

end OAI
