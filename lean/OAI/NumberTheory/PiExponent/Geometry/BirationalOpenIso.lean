import OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing

namespace OAI

noncomputable section
namespace PiExponent.BirationalOpenIso
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem exists_open_iso_of_generic_inverse (f : Y ⟶ X)
    [LocallyOfFiniteType f] [IsSeparated f]
    (e : Y.functionField ≃+* X.functionField)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y) ≫ f = X.fromSpecStalk (genericPoint X)) :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (f ∣_ U) := by
  let η : Spec X.functionField ⟶ Y :=
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y)
  have hηf : η ≫ f = X.fromSpecStalk (genericPoint X) ≫ 𝟙 X := by
    simpa only [η, Category.assoc, Category.comp_id] using! he
  obtain ⟨U, hU, g, hη, hg⟩ := spread_out_of_isGermInjective' (𝟙 X) f η hηf
  simp only [Category.comp_id] at hg
  let V : Y.Opens := f ⁻¹ᵁ U
  have hrange : Set.range g ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨g x, ?_⟩, rfl⟩
    change f (g x) ∈ U
    have hpoint := congrArg (fun k : U.toScheme ⟶ X => k x) hg
    change f (g x) = x.1 at hpoint
    rw [hpoint]
    exact x.2
  let s : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι g hrange
  have hs : s ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hsr : s ≫ (f ∣_ U) = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hs, hg, Category.id_comp]
  let : IsDominant (Y.fromSpecStalk (genericPoint Y)) :=
    CurveStalkGluing.isDominant_fromSpecFunctionField
  have hηdom : IsDominant η := by
    let : IsIso (CommRingCat.ofHom e.toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr e.bijective
    dsimp only [η]
    infer_instance
  have : IsDominant (U.fromSpecStalkOfMem (genericPoint X) hU ≫ g) := by
    rw [← hη]
    exact hηdom
  have : IsDominant g := IsDominant.of_comp (U.fromSpecStalkOfMem (genericPoint X) hU) g
  have : IsDominant (s ≫ V.ι) := by rw [hs]; infer_instance
  have : IsDominant s := IsDominant.of_comp_of_isOpenImmersion s V.ι
  have hbase : ((f ∣_ U) ≫ s) ≫ (f ∣_ U) = (𝟙 V.toScheme) ≫ (f ∣_ U) := by
    rw [Category.assoc, hsr, Category.comp_id, Category.id_comp]
  have hdense : s ≫ ((f ∣_ U) ≫ s) = s ≫ 𝟙 V.toScheme := by
    rw [← Category.assoc, hsr, Category.id_comp, Category.comp_id]
  have hrs : (f ∣_ U) ≫ s = 𝟙 V.toScheme :=
    ext_of_isDominant_of_isSeparated (f ∣_ U) hbase s hdense
  exact ⟨U, hU, ⟨⟨s, hrs, hsr⟩⟩⟩

end PiExponent.BirationalOpenIso

end

end OAI
