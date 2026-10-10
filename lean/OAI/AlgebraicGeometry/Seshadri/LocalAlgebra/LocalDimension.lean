import Mathlib

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry TopologicalSpace Order

lemma scheme_dimension_eq_point_dimension (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

lemma scheme_dimension_le_of_neighborhoods (X : Scheme) (d : WithBot ℕ∞)
    (h : ∀ x : X, ∃ (U : Scheme) (f : U ⟶ X), IsOpenImmersion f ∧
      x ∈ Set.range f ∧ topologicalKrullDim U ≤ d) : topologicalKrullDim X ≤ d := by
  rw [scheme_dimension_eq_point_dimension, Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  obtain ⟨U,f,hf,⟨y,rfl⟩,hd⟩ := h x
  let := hf
  rw [AlgebraicGeometry.coheight_eq_of_isOpenImmersion]
  exact (Order.coheight_le_krullDim y).trans ((scheme_dimension_eq_point_dimension U) ▸ hd)

lemma subscheme_dimension_le_of_affine_neighborhoods {X : Scheme}
    (I : X.IdealSheafData) (d : WithBot ℕ∞)
    (h : ∀ x : I.subscheme, ∃ U : X.affineOpens, I.subschemeι x ∈ U.1 ∧
      ringKrullDim (Γ(X,U.1) ⧸ I.ideal U) ≤ d) :
    topologicalKrullDim I.subscheme ≤ d := by
  apply scheme_dimension_le_of_neighborhoods
  intro x
  obtain ⟨U,hx,hd⟩ := h x
  let := I.subschemeCover.map_prop U
  refine ⟨_, I.subschemeCover.f U,inferInstance,?_,?_⟩
  · change x ∈ (I.subschemeCover.f U).opensRange
    rw [I.opensRange_subschemeCover_map]
    exact hx
  · exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).le.trans hd

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
