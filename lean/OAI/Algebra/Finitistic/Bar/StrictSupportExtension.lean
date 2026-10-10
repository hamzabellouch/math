import Mathlib.Algebra.Homology.Embedding.StupidTrunc

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace DerivedBar
universe u v w w'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type w} {ι' : Type w'} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : c.Embedding c') [e.IsRelIff] (K : HomologicalComplex C c')
  [K.IsStrictlySupported e]

/-- Actual component isomorphisms for extension after restriction of a complex
which is already zero outside the index embedding. -/
def supportedExtensionXIso (j : ι') : ((K.restriction e).extend e).X j ≅ K.X j := by
  classical
  exact if h : ∃ i, e.f i=j then
    (K.restriction e).extendXIso e h.choose_spec ≪≫ K.restrictionXIso e h.choose_spec
  else
    ((K.restriction e).isZero_extend_X e j (not_exists.mp h)).iso
      (K.isZero_X_of_isStrictlySupported e j (not_exists.mp h))

theorem supportedExtensionXIso_image (i : ι) (j : ι') (hi : e.f i=j) :
    supportedExtensionXIso e K j =
      (K.restriction e).extendXIso e hi ≪≫ K.restrictionXIso e hi := by
  classical
  unfold supportedExtensionXIso
  split_ifs with h
  · have hh : h.choose=i := e.injective_f (h.choose_spec.trans hi.symm)
    subst i
    rfl
  · exact (h ⟨i,hi⟩).elim

/-- The genuine chain isomorphism, including all boundary differentials. -/
def strictSupportExtensionIso : (K.restriction e).extend e ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (supportedExtensionXIso e K) (by
    intro i' j' hij
    classical
    by_cases hi : ∃ i, e.f i=i'
    · by_cases hj : ∃ j, e.f j=j'
      · obtain ⟨i,hi⟩ := hi
        obtain ⟨j,hj⟩ := hj
        rw [supportedExtensionXIso_image e K i i' hi, supportedExtensionXIso_image e K j j' hj,
          extend_d_eq _ e hi hj, restriction_d_eq _ e hi hj]
        simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
      · exact (K.isZero_X_of_isStrictlySupported e j' (not_exists.mp hj)).eq_of_tgt _ _
    · exact ((K.restriction e).isZero_extend_X e i' (not_exists.mp hi)).eq_of_src _ _)
end DerivedBar

end

end OAI
