import Mathlib

namespace OAI


                                     
section

namespace MaximalSeshadri.ModuleLocal
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X : Scheme.{0}} {M N : X.Modules}

lemma app_zero_of_restrict (φ : M ⟶ N) (U W : X.Opens) (hW : W ≤ U)
    (h : (Scheme.Modules.restrictFunctor U.ι).map φ = 0) : φ.app W = 0 := by
  have hz := congrArg (fun q : M.restrict U.ι ⟶ N.restrict U.ι =>
    q.app (U.ι ⁻¹ᵁ W)) h
  have he : U.ι ''ᵁ U.ι ⁻¹ᵁ W = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  change φ.app (U.ι ''ᵁ U.ι ⁻¹ᵁ W) = 0 at hz
  suffices hh : ∀ A : X.Opens, A = W → φ.app A = 0 → φ.app W = 0 from hh _ he hz
  intro A hA hφ
  subst A
  exact hφ

lemma eq_zero_of_local (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (Scheme.Modules.restrictFunctor U.ι).map φ = 0) : φ = 0 := by
  ext W m
  change φ.app W m = 0
  let F : (X : TopCat).Sheaf AddCommGrpCat := (SheafOfModules.toSheaf X.ringCatSheaf).obj N
  apply TopCat.Presheaf.section_ext F W (φ.app W m) 0
  intro x hx
  obtain ⟨U,hxU,hU⟩ := h x
  let V : X.Opens := W ⊓ U
  have hv : φ.app V = 0 := app_zero_of_restrict φ U V inf_le_right hU
  change N.presheaf.germ W x hx (φ.app W m) = N.presheaf.germ W x hx 0
  rw [← TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE (show V ≤ W from inf_le_left))
    x (show x ∈ V from ⟨hx,hxU⟩)]
  have hn := CategoryTheory.congr_fun (φ.mapPresheaf.naturality
    (homOfLE (show V ≤ W from inf_le_left)).op) m
  change φ.app V (M.presheaf.map (homOfLE inf_le_left).op m) =
    N.presheaf.map (homOfLE inf_le_left).op (φ.app W m) at hn
  rw [← hn,hv]
  simp

lemma epi_of_local (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Epi ((Scheme.Modules.restrictFunctor U.ι).map φ)) : Epi φ := by
  apply (Preadditive.epi_iff_cancel_zero _).mpr
  intro P g hg
  apply eq_zero_of_local
  intro x
  obtain ⟨U,hx,hU⟩ := h x
  let := hU
  refine ⟨U,hx,?_⟩
  apply (cancel_epi ((Scheme.Modules.restrictFunctor U.ι).map φ)).mp
  rw [← Functor.map_comp,hg,Functor.map_zero,comp_zero]

lemma mono_of_local (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((Scheme.Modules.restrictFunctor U.ι).map φ)) : Mono φ := by
  apply (Preadditive.mono_iff_cancel_zero _).mpr
  intro P g hg
  apply eq_zero_of_local
  intro x
  obtain ⟨U,hx,hU⟩ := h x
  let := hU
  refine ⟨U,hx,?_⟩
  apply (cancel_mono ((Scheme.Modules.restrictFunctor U.ι).map φ)).mp
  rw [← Functor.map_comp,hg,Functor.map_zero,zero_comp]

lemma isIso_of_local (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) : IsIso φ := by
  have : Epi φ := epi_of_local φ (fun x => by
    obtain ⟨U,hx,hU⟩ := h x
    let := hU
    exact ⟨U,hx,inferInstance⟩)
  have : Mono φ := mono_of_local φ (fun x => by
    obtain ⟨U,hx,hU⟩ := h x
    let := hU
    exact ⟨U,hx,inferInstance⟩)
  exact isIso_of_mono_of_epi φ

lemma exact_of_local (S : ShortComplex X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (S.map (Scheme.Modules.restrictFunctor U.ι)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply eq_zero_of_local
  intro x
  obtain ⟨U,hx,hU⟩ := h x
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) := by
    have : PreservesFiniteLimits
        (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.toPresheaf U.toScheme) := by
      change PreservesFiniteLimits
        (Scheme.Modules.toPresheaf X ⋙ (Functor.whiskeringLeft _ _ _).obj U.ι.opensFunctor.op)
      have : PreservesFiniteLimits (Scheme.Modules.toPresheaf X) := inferInstance
      have : PreservesFiniteLimits
          ((Functor.whiskeringLeft _ _ Ab).obj U.ι.opensFunctor.op) := inferInstance
      exact comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_reflects_of_preserves _
      (Scheme.Modules.toPresheaf U.toScheme)
  have hz : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj S.homology) :=
    ((ShortComplex.exact_iff_isZero_homology _).mp hU).of_iso
      (S.mapHomologyIso (Scheme.Modules.restrictFunctor U.ι)).symm
  refine ⟨U,hx,?_⟩
  rw [CategoryTheory.Functor.map_id]
  exact hz.eq_of_src _ _

end
end MaximalSeshadri.ModuleLocal

end

end OAI
