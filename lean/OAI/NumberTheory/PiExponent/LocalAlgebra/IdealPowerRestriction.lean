import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

def closedQuotientRestrictIso {I J : Y.IdealSheafData} (h : I ≤ J)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (cokernel (closedMap h)).restrict f ≅
      cokernel (closedMap (Scheme.IdealSheafData.comap_mono f h)) :=
  PreservesCokernel.iso (Scheme.Modules.restrictFunctor f) (closedMap h) ≪≫
    cokernel.mapIso _ _ (closedModuleRestrictIso I f) (closedModuleRestrictIso J f)
      (closedModuleRestrictIso_naturality h f)

def closedQuotientCongr {I J I' J' : X.IdealSheafData} (h : I ≤ J) (h' : I' ≤ J')
    (hI : I = I') (hJ : J = J') : cokernel (closedMap h) ≅ cokernel (closedMap h') := by
  subst I'
  subst J'
  exact Iso.refl _

def powerLayerRestrictIso (I : Y.IdealSheafData) (n : ℕ)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (powerLayer I n).restrict f ≅ powerLayer (I.comap f) n :=
  closedQuotientRestrictIso (fun _U => Ideal.pow_le_pow_right (Nat.le_succ n)) f ≪≫
    closedQuotientCongr _ _ (IdealPullback.comap_pow I f (n+1)) (IdealPullback.comap_pow I f n)

theorem powerLayer_restrict_smul_eq_zero (I : Y.IdealSheafData) (n : ℕ)
    (f : X ⟶ Y) [IsOpenImmersion f] (r : Γ(X,⊤))
    (hr : (I.comap f).subschemeι.appTop r = 0)
    (x : Γ((powerLayer I n).restrict f,⊤)) : r • x = 0 := by
  let e := powerLayerRestrictIso I n f
  have hz : r • e.hom.app ⊤ x = 0 := by
    have h := congrArg (fun a : powerLayer (I.comap f) n ⟶ powerLayer (I.comap f) n =>
      a.app ⊤ (e.hom.app ⊤ x)) (powerLayer_smul_id_eq_zero (I.comap f) n r hr)
    change (X.presheaf.map (𝟙 (op ⊤)) r) • e.hom.app ⊤ x = 0 at h
    have hid : X.presheaf.map (𝟙 (op ⊤)) r = r :=
      congrArg (fun g : Γ(X,⊤) ⟶ Γ(X,⊤) => g r) (X.presheaf.map_id (op ⊤))
    exact (congrArg (fun a : Γ(X,⊤) => a • e.hom.app ⊤ x) hid).symm.trans h
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  exact (e.hom.app_smul r x).trans (hz.trans (map_zero _).symm)

theorem ker_subscheme_morphismRestrict (I : Y.IdealSheafData) (U : Y.Opens) :
    (I.subschemeι ∣_ U).ker = I.comap U.ι := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion I.subschemeι
    (I.subschemeι ∣_ U) (I.subschemeι ⁻¹ᵁ U).ι U.ι
    (isPullback_morphismRestrict I.subschemeι U), I.ker_subschemeι,
    I.ideal_comap_of_isOpenImmersion]

theorem ker_appTop_subscheme_morphismRestrict (I : Y.IdealSheafData) (U : Y.affineOpens) :
    RingHom.ker (I.subschemeι ∣_ U.1).appTop.hom =
      RingHom.ker (I.comap U.1.ι).subschemeι.appTop.hom := by
  let : IsAffine U.1.toScheme := U.2
  exact (Scheme.Hom.ker_apply (I.subschemeι ∣_ U.1) ⟨⊤,isAffineOpen_top _⟩).symm.trans
    ((congrArg (fun J : U.1.toScheme.IdealSheafData => J.ideal ⟨⊤,isAffineOpen_top _⟩)
      (ker_subscheme_morphismRestrict I U.1)).trans
      ((I.comap U.1.ι).ker_subschemeι_app ⟨⊤,isAffineOpen_top _⟩).symm)

theorem powerLayer_restrict_kernel_smul_eq_zero (I : Y.IdealSheafData) (n : ℕ)
    (U : Y.affineOpens) (r : Γ(U.1.toScheme,⊤))
    (hr : (I.subschemeι ∣_ U.1).appTop r = 0)
    (x : Γ((powerLayer I n).restrict U.1.ι,⊤)) : r • x = 0 := by
  apply powerLayer_restrict_smul_eq_zero I n U.1.ι r _ x
  apply RingHom.mem_ker.mp
  rw [← ker_appTop_subscheme_morphismRestrict I U]
  exact hr

end
end PiExponentSeshadri.IdealModule

end OAI
