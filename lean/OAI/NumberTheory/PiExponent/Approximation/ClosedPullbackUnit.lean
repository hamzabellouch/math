import OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange

namespace OAI

namespace PiExponentSeshadri.ClosedPullbackUnit
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

def opensEquivalence [IsIso f.base] : X.Opens ≌ Y.Opens :=
  Opens.mapMapIso (asIso f.base)

lemma preimage_surjective [IsIso f.base] :
    Function.Surjective (fun U : X.Opens => f ⁻¹ᵁ U) := by
  intro V
  refine ⟨(opensEquivalence f).inverse.obj V, ?_⟩
  exact le_antisymm (leOfHom ((opensEquivalence f).counitIso.app V).hom)
    (leOfHom ((opensEquivalence f).counitIso.app V).inv)

def additivePreimage [IsIso f.base] {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N) :
    M.presheaf ⟶ N.presheaf := by
  let : (Opens.map f.base).IsEquivalence := (opensEquivalence f).isEquivalence_functor
  exact ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj (Opens.map f.base).op).preimage a.mapPresheaf

lemma additivePreimage_app [IsIso f.base] {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N)
    (U : X.Opens) : (additivePreimage f a).app (op (f ⁻¹ᵁ U)) = a.app U := by
  let : (Opens.map f.base).IsEquivalence := (opensEquivalence f).isEquivalence_functor
  exact congrArg (fun b : (Opens.map f.base).op ⋙ M.presheaf ⟶
      (Opens.map f.base).op ⋙ N.presheaf => b.app (op U))
    (((Functor.whiskeringLeft _ _ AddCommGrpCat).obj (Opens.map f.base).op).map_preimage (X := M.presheaf) (Y := N.presheaf) a.mapPresheaf)

lemma additivePreimage_smul [IsClosedImmersion f] [IsIso f.base]
    {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N)
    (V : Y.Opens) (r : Γ(Y,V)) (m : Γ(M,V)) :
    (additivePreimage f a).app (op V) (r • m) =
      r • (additivePreimage f a).app (op V) m := by
  obtain ⟨U, rfl⟩ := preimage_surjective f V
  apply N.isSheaf.section_ext
  intro y hy
  obtain ⟨W, hW, hyW, hWU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := f y) (U := U) hy
  let j : W ⟶ U := homOfLE hWU
  let k : f ⁻¹ᵁ W ⟶ f ⁻¹ᵁ U := (Opens.map f.base).map j
  refine ⟨f ⁻¹ᵁ W, leOfHom k, hyW, ?_⟩
  have hn (z : Γ(M,f ⁻¹ᵁ U)) :
      (additivePreimage f a).app (op (f ⁻¹ᵁ W)) (M.presheaf.map k.op z) =
        N.presheaf.map k.op ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) z) :=
    CategoryTheory.congr_fun ((additivePreimage f a).naturality k.op) z
  have hs : N.presheaf.map k.op (r • (additivePreimage f a).app (op (f ⁻¹ᵁ U)) m) =
      Y.presheaf.map k.op r • N.presheaf.map k.op ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) m) :=
    N.val.map_smul k.op r ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) m)
  change N.presheaf.map k.op ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) (r • m)) =
    N.presheaf.map k.op (r • (additivePreimage f a).app (op (f ⁻¹ᵁ U)) m)
  rw [← hn, hs, ← hn, additivePreimage_app]
  obtain ⟨c, hc⟩ := f.app_surjective W hW (Y.presheaf.map k.op r)
  have hm := M.val.map_smul k.op r m
  change M.presheaf.map k.op (r • m) = Y.presheaf.map k.op r • M.presheaf.map k.op m at hm
  rw [hm, ← hc]
  exact a.app_smul (r := c) (x := M.presheaf.map k.op m)

def modulePreimage [IsClosedImmersion f] [IsIso f.base] {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N) :
    M ⟶ N where
  val.app V := ModuleCat.ofHom (X := M.val.obj V) (Y := N.val.obj V)
    { toAddHom := ((additivePreimage f a).app V).hom.toAddHom
      map_smul' := fun r m => additivePreimage_smul f a V.unop r m }
  val.naturality {V W} j := by
    ext m
    exact CategoryTheory.congr_fun ((additivePreimage f a).naturality j) m

def pushforwardFullyFaithful [IsClosedImmersion f] [IsIso f.base] :
    (Scheme.Modules.pushforward f).FullyFaithful where
  preimage a := modulePreimage f a
  map_preimage a := by
    ext U m
    exact CategoryTheory.congr_fun (additivePreimage_app f a U) m
  preimage_map a := by
    apply Scheme.Modules.hom_ext
    intro V
    obtain ⟨U, rfl⟩ := preimage_surjective f V
    exact additivePreimage_app f ((Scheme.Modules.pushforward f).map a) U

theorem counit_isIso [IsClosedImmersion f] (hf : Function.Surjective f) :
    IsIso (Scheme.Modules.pullbackPushforwardAdjunction f).counit := by
  let : IsIso f.base := (TopCat.isIso_iff_isHomeomorph f.base).mpr
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨f.isClosedEmbedding.isEmbedding, hf⟩)
  let := (pushforwardFullyFaithful f).full
  let := (pushforwardFullyFaithful f).faithful
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).counit_isIso_of_R_fully_faithful

theorem unit_isIso_of_pushforward [IsClosedImmersion f] (hf : Function.Surjective f)
    {M : X.Modules} {N : Y.Modules}
    (e : M ≅ (Scheme.Modules.pushforward f).obj N) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  let : IsIso (Scheme.Modules.pullbackPushforwardAdjunction f).counit := counit_isIso f hf
  let := (Scheme.Modules.pullbackPushforwardAdjunction f).fullyFaithfulROfIsIsoCounit.full
  let := (Scheme.Modules.pullbackPushforwardAdjunction f).fullyFaithfulROfIsIsoCounit.faithful
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).isIso_unit_app_of_iso e

lemma subscheme_surjective_of_support_top (I : X.IdealSheafData) (hI : I.support = ⊤) :
    Function.Surjective I.subschemeι := by
  rw [← Set.range_eq_univ, I.range_subschemeι, hI]
  rfl

theorem subscheme_counit_isIso (I : X.IdealSheafData) (hI : I.support = ⊤) :
    IsIso (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).counit :=
  counit_isIso I.subschemeι (subscheme_surjective_of_support_top I hI)

theorem subscheme_unit_isIso_of_pushforward (I : X.IdealSheafData) (hI : I.support = ⊤)
    {M : X.Modules} {N : I.subscheme.Modules}
    (e : M ≅ (Scheme.Modules.pushforward I.subschemeι).obj N) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app M) :=
  unit_isIso_of_pushforward I.subschemeι (subscheme_surjective_of_support_top I hI) e

end
end PiExponentSeshadri.ClosedPullbackUnit

end OAI
