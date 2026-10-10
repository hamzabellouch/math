import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedValue

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}

theorem functionsOnOpenEquiv_global
    (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j] (s : Γ(Y, ⊤)) :
    functionsOnOpenEquiv j (Y.presheaf.map (homOfLE le_top).op s) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom (j.appTop s) := by
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (j.isoOpensRange.hom.appTop
      (j.opensRange.topIso.inv (Y.presheaf.map (homOfLE le_top).op s))) = _
  have ht : j.opensRange.topIso.inv (Y.presheaf.map (homOfLE le_top).op s) =
      j.opensRange.ι.appTop s := by
    change (Y.presheaf.map (homOfLE le_top).op ≫
      j.opensRange.topIso.inv) s = _
    simp only [Scheme.Opens.topIso_inv]
    erw [← Functor.map_comp, ← op_comp]
    rfl
  rw [ht]
  have hj := congrArg (fun f => f.appTop) j.isoOpensRange_hom_ι
  rw [Scheme.Hom.comp_appTop] at hj
  exact congrArg (fun f => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (f s)) hj

theorem functionsOnOpenEquiv_pullback
    (f : Y ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ)) (r : R) :
    functionsOnOpenEquiv j (Y.presheaf.map (homOfLE le_top).op
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) = φ r := by
  rw [functionsOnOpenEquiv_global]
  have h := congrArg (fun g => g.appTop) hf
  rw [Scheme.Hom.comp_appTop] at h
  have hv := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (g ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) h
  refine hv.trans ?_
  have hn := CategoryTheory.congr_fun
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Spec.map (CommRingCat.ofHom φ)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
    φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) at hn
  exact hn.trans (congrArg φ
    (CategoryTheory.congr_fun (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id r))

end
end PiExponent.ExceptionalAffineChart

end OAI
