import OAI.NumberTheory.PiExponent.Approximation.SectionOpens

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma trivialModule_restriction_injective [IsIntegral X] (M : X.Modules)
    (e : M ≅ structureSheaf X) {U V : X.Opens} (i : U ⟶ V) [Nonempty U] :
    Function.Injective (M.presheaf.map i.op) := by
  intro s t h
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf X).mapIso e).app (Opposite.op V)).hom).injective
  have hn := e.hom.mapPresheaf.naturality i.op
  have heq := congrArg (fun a => e.hom.app U a) h
  have hh (a : Γ(M, V)) :
      e.hom.app U (M.presheaf.map i.op a) =
        X.presheaf.map i.op (e.hom.app V a) := by
    exact CategoryTheory.congr_fun hn a
  rw [hh, hh] at heq
  exact map_injective_of_isIntegral X i heq

theorem LineBundle.restriction_injective [IsIntegral X] (L : LineBundle X)
    {U V : X.Opens} (i : U ⟶ V) [Nonempty U] :
    Function.Injective (L.sheaf.presheaf.map i.op) := by
  intro s t h
  apply L.sheaf.isSheaf.section_ext
  intro x hx
  obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
  let f := T.ι
  let U' : T.toScheme.Opens := f ⁻¹ᵁ U
  let V' : T.toScheme.Opens := f ⁻¹ᵁ V
  have hU' : Nonempty U' := by
    obtain ⟨y, hyT, hyU⟩ := nonempty_preirreducible_inter T.isOpen U.isOpen
      ⟨x, hxT⟩ (by obtain ⟨u⟩ := ‹Nonempty U›; exact ⟨u.val, u.property⟩)
    exact ⟨⟨⟨y, hyT⟩, hyU⟩⟩
  have : Nonempty U' := hU'
  have : Nonempty T := ⟨⟨x, hxT⟩⟩
  let j : U' ⟶ V' := homOfLE (fun _ h => leOfHom i h)
  let W := f ''ᵁ V'
  have hWV : W ≤ V := f.image_preimage_le V
  refine ⟨W, hWV, ?_, ?_⟩
  · exact ⟨⟨x, hxT⟩, hx, rfl⟩
  · apply trivialModule_restriction_injective (L.sheaf.restrict f) e j
    change L.sheaf.presheaf.map ((f.opensFunctor.map j).op)
        (L.sheaf.presheaf.map (homOfLE hWV).op s) =
      L.sheaf.presheaf.map ((f.opensFunctor.map j).op)
        (L.sheaf.presheaf.map (homOfLE hWV).op t)
    have hh := congrArg
      (fun a => L.sheaf.presheaf.map (homOfLE (f.image_preimage_le U)).op a) h
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hh ⊢
    have eq : i.op ≫ (homOfLE (f.image_preimage_le U)).op =
        (homOfLE hWV).op ≫ (f.opensFunctor.map j).op := Subsingleton.elim _ _
    rw [eq] at hh
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hh

theorem LineBundle.section_restriction_injective [IsIntegral X] (L : LineBundle X)
    (U : X.Opens) [Nonempty U] :
    Function.Injective (fun s : GlobalSections X L.sheaf => s.app U (1 : Γ(X, U))) := by
  intro s t h
  have natural (s : GlobalSections X L.sheaf) (V : X.Opens) :
      s.app V (1 : Γ(X, V)) = L.sheaf.presheaf.map
        (homOfLE (show V ≤ ⊤ from le_top)).op (s.app ⊤ (1 : Γ(X, ⊤))) := by
    have hs := CategoryTheory.congr_fun (s.mapPresheaf.naturality
      (homOfLE (show V ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
    change s.app V (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op 1) =
      L.sheaf.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (s.app ⊤ (1 : Γ(X, ⊤))) at hs
    simpa only [map_one, ConcreteCategory.comp_apply] using hs
  have ht : s.app ⊤ (1 : Γ(X, ⊤)) = t.app ⊤ (1 : Γ(X, ⊤)) := by
    apply L.restriction_injective (homOfLE (show U ≤ ⊤ from le_top))
    rw [← natural s U, ← natural t U]
    exact h
  ext V a
  change Γ(X, V) at a
  have hv : s.app V (1 : Γ(X, V)) = t.app V (1 : Γ(X, V)) := by
    rw [natural s, natural t, ht]
  have scalar (s : GlobalSections X L.sheaf) :
      s.app V a = a • s.app V (1 : Γ(X, V)) := by
    have hs := s.app_smul (r := a) (x := (1 : Γ(X, V)))
    change s.app V (a * 1 : Γ(X, V)) = _ at hs
    simpa only [mul_one] using hs
  rw [scalar s, scalar t, hv]

variable [IsIntegral X]

theorem LineBundle.noZeroSMulDivisors (L : LineBundle X)
    (U : X.Opens) [Nonempty U] : NoZeroSMulDivisors Γ(X, U) Γ(L.sheaf, U) where
  eq_zero_or_eq_zero_of_smul_eq_zero {a m} h := by
    obtain ⟨x, hx⟩ := ‹Nonempty U›
    obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
    let V : T.toScheme.Opens := T.ι ⁻¹ᵁ U
    have : Nonempty V := ⟨⟨⟨x, hxT⟩, hx⟩⟩
    have : Nonempty T := ⟨⟨x, hxT⟩⟩
    let W : X.Opens := T.ι ''ᵁ V
    have : Nonempty W := ⟨⟨x, ⟨x, hxT⟩, hx, rfl⟩⟩
    let i : W ⟶ U := homOfLE (T.ι.image_preimage_le U)
    let ar : Γ(X, W) := X.presheaf.map i.op a
    let mr : Γ(L.sheaf, W) := L.sheaf.presheaf.map i.op m
    have hr : ar • mr = 0 := by
      have hh := congrArg (fun z => L.sheaf.presheaf.map i.op z) h
      simpa only [L.sheaf.map_smul, map_zero] using hh
    let ar' : Γ(T.toScheme, V) := (T.ι.appIso V).hom ar
    let mr' : Γ(L.sheaf.restrict T.ι, V) := (L.sheaf.restrictAppIso T.ι V).inv mr
    let cr : Γ(T.toScheme, V) := e.hom.app V mr'
    have hr' : ar' • mr' = 0 := by
      rw [← Scheme.Modules.smul_restrictAppIso_inv_apply]
      simp only [hr, map_zero]
    have hmul : ar' * cr = 0 := by
      have hh := e.hom.app_smul (r := ar') (x := mr')
      change e.hom.app V (ar' • mr') = ar' * cr at hh
      rw [hr', map_zero] at hh
      exact hh.symm
    rcases mul_eq_zero.mp hmul with ha | hm
    · left
      apply map_injective_of_isIntegral X i
      have hinj := (ConcreteCategory.bijective_of_isIso (T.ι.appIso V).hom).injective
      apply hinj
      simpa only [map_zero] using ha
    · right
      apply L.restriction_injective i
      have hinj := (ConcreteCategory.bijective_of_isIso
        (((Scheme.Modules.toPresheaf T.toScheme).mapIso e).app (Opposite.op V)).hom).injective
      apply (ConcreteCategory.bijective_of_isIso (L.sheaf.restrictAppIso T.ι V).inv).injective
      apply hinj
      change cr = e.hom.app V ((L.sheaf.restrictAppIso T.ι V).inv
        (L.sheaf.presheaf.map i.op 0))
      refine hm.trans ?_
      simp only [map_zero]
      rfl

theorem LineBundle.mono_section (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) : Mono s := by
  have hmono : Mono s.val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    by_cases hU : Nonempty U.unop
    · let := hU
      let := L.noZeroSMulDivisors U.unop
      intro a b hab
      change Γ(X, U.unop) at a b
      have hc : s.app U.unop (1 : Γ(X, U.unop)) ≠ 0 := by
        intro h
        apply hs
        apply L.section_restriction_injective U.unop
        exact h
      have hscalar (a : Γ(X, U.unop)) : s.app U.unop a =
          a • s.app U.unop (1 : Γ(X, U.unop)) := by
        have hh := s.app_smul (r := a) (x := (1 : Γ(X, U.unop)))
        change s.app U.unop (a * 1 : Γ(X, U.unop)) = _ at hh
        simpa only [mul_one] using hh
      have heq : s.app U.unop a = s.app U.unop b := hab
      rw [hscalar a, hscalar b] at heq
      exact (smul_left_injective Γ(X, U.unop) hc) heq
    · have he : U.unop = ⊥ := by
        apply Opens.ext
        ext x
        exact ⟨fun hx => (hU ⟨⟨x, hx⟩⟩).elim, fun h => h.elim⟩
      have : Subsingleton Γ(X, U.unop) := by rw [he]; infer_instance
      intro a b _
      change Γ(X, U.unop) at a b
      exact Subsingleton.elim a b
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map hmono

end Geometry

namespace Frames
open CategoryTheory AlgebraicGeometry
variable {X Y : Scheme}
lemma coefficient_injective {M : X.Modules} (e : M ≅ O X) :
    Function.Injective (coefficient e) := by
  intro s t h
  apply (cancel_mono e.hom).1
  exact endValue_injective h
lemma coefficient_zero {M : X.Modules} (e : M ≅ O X) :
    coefficient e (0 : O X ⟶ M) = 0 := by
  rw [coefficient, CategoryTheory.Limits.zero_comp]
  rfl
lemma restrictSection_zero (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules} :
    restrictSection φ (0 : O X ⟶ M) = 0 := by
  ext U a
  rfl
end Frames

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y : Scheme}
lemma LineBundle.restrict_sections_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y] :
    Function.Injective (fun s : GlobalSections X L.sheaf =>
      (Scheme.Modules.restrictFunctor f).map s) := by
  intro s t h
  let U : X.Opens := f ''ᵁ ⊤
  have : Nonempty U := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    exact ⟨⟨f y, y, Set.mem_univ y, rfl⟩⟩
  apply L.section_restriction_injective U
  have he := congrArg (fun s : (structureSheaf X).restrict f ⟶ L.sheaf.restrict f =>
    s.app ⊤ (1 : Γ(X, U))) h
  exact he

lemma LineBundle.restricted_coefficient_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    Function.Injective (fun s : GlobalSections X L.sheaf => coefficient e (restrictSection f s)) := by
  intro s t h
  apply L.restrict_sections_injective f
  let u : (structureSheaf X).restrict f ≅ structureSheaf Y :=
    Scheme.Modules.restrictUnitIso f
  apply (cancel_epi u.inv).mp
  exact coefficient_injective e h

lemma LineBundle.isoOpen_ne_bot [IsIntegral X] (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) : PiExponentSeshadri.SectionOpens.isoOpen s ≠ ⊥ := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨V,hx,⟨e⟩⟩ := L.locallyRankOne x
  let : Nonempty V := ⟨⟨x,hx⟩⟩
  have hc : coefficient e (restrictSection V.ι s) ≠ 0 := by
    intro h
    apply hs
    apply L.restricted_coefficient_injective V.ι e
    have hz : coefficient e (restrictSection V.ι (0 : O X ⟶ L.sheaf)) = 0 :=
      (congrArg (coefficient e) (restrictSection_zero V.ι)).trans (coefficient_zero e)
    exact h.trans hz.symm
  intro hz
  have he := preimage_isoOpen s V.ι e
  rw [hz] at he
  have hb : V.toScheme.basicOpen (coefficient e (restrictSection V.ι s)) = ⊥ := by
    simpa only [Scheme.Hom.preimage_bot] using he.symm
  exact hc (eq_zero_of_basicOpen_eq_bot _ hb)

theorem LineBundle.sectionOpen_nonempty [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    Nonempty (sectionOpen X s) := by
  have h := L.isoOpen_ne_bot s hs
  by_contra hn
  apply h
  apply TopologicalSpace.Opens.ext
  ext x
  exact ⟨fun hx => hn ⟨⟨x,hx⟩⟩, fun hx => hx.elim⟩
end Geometry

end PiExponentSeshadri

end

end OAI
