import OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology

namespace OAI

namespace PiExponent.GeometrySupport.CechOne

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

theorem hom_glue {J : Type u} (U : J → Opens X) (V : Opens X)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (M : SheafOfModules.{u} R) (f : ∀ i, freeOpen R (U i) ⟶ M)
    (hf : ∀ i j, freeOpenMap R (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)) ≫ f i =
      freeOpenMap R (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)) ≫ f j) :
    ∃ g : freeOpen R V ⟶ M, ∀ i, freeOpenMap R (homOfLE (hUV i)) ≫ g = f i := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := (SheafOfModules.toSheaf R).obj M
  let sf (i : J) := freeOpenEquiv R M (U i) (f i)
  have hc : TopCat.Presheaf.IsCompatible F.obj U sf := by
    intro i j
    change M.val.map (homOfLE inf_le_left).op (sf i) =
      M.val.map (homOfLE inf_le_right).op (sf j)
    rw [← freeOpenEquiv_naturality, ← freeOpenEquiv_naturality, hf i j]
  obtain ⟨s, hs, _⟩ := F.existsUnique_gluing' U V (fun i => homOfLE (hUV i)) hcover sf hc
  refine ⟨(freeOpenEquiv R M V).symm s, fun i => ?_⟩
  apply (freeOpenEquiv R M (U i)).injective
  rw [freeOpenEquiv_naturality]
  exact (congrArg (M.val.map (homOfLE (hUV i)).op)
    ((freeOpenEquiv R M V).apply_symm_apply s)).trans (hs i)

def restrictHom {M : SheafOfModules.{u} R} {U V : Opens X}
    (h : U ≤ V) (f : freeOpen R V ⟶ M) : freeOpen R U ⟶ M :=
  freeOpenMap R (homOfLE h) ≫ f

@[simp] theorem restrictHom_restrictHom {M : SheafOfModules.{u} R} {U V W : Opens X}
    (h : U ≤ V) (k : V ≤ W) (f : freeOpen R W ⟶ M) :
    restrictHom R h (restrictHom R k f) = restrictHom R (h.trans k) f := by
  change (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor R).map (homOfLE h) ≫
      (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor R).map (homOfLE k) ≫ f =
    (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor R).map (homOfLE (h.trans k)) ≫ f
  erw [← Category.assoc, ← Functor.map_comp]
  rfl

@[simp] theorem restrictHom_comp {M N : SheafOfModules.{u} R} {U V : Opens X}
    (h : U ≤ V) (f : freeOpen R V ⟶ M) (g : M ⟶ N) :
    restrictHom R h (f ≫ g) = restrictHom R h f ≫ g := by
  simp only [restrictHom, Category.assoc]

@[simp] theorem restrictHom_add {M : SheafOfModules.{u} R} {U V : Opens X}
    (h : U ≤ V) (f g : freeOpen R V ⟶ M) :
    restrictHom R h (f + g) = restrictHom R h f + restrictHom R h g := by
  simp only [restrictHom, Preadditive.comp_add]

@[simp] theorem restrictHom_sub {M : SheafOfModules.{u} R} {U V : Opens X}
    (h : U ≤ V) (f g : freeOpen R V ⟶ M) :
    restrictHom R h (f - g) = restrictHom R h f - restrictHom R h g := by
  simp only [restrictHom, Preadditive.comp_sub]

theorem hom_ext {J : Type u} (U : J → Opens X) (V : Opens X)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (M : SheafOfModules.{u} R) (f g : freeOpen R V ⟶ M)
    (hfg : ∀ i, restrictHom R (hUV i) f = restrictHom R (hUV i) g) : f = g := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := (SheafOfModules.toSheaf R).obj M
  apply (freeOpenEquiv R M V).injective
  apply F.eq_of_locally_eq' U V (fun i => homOfLE (hUV i)) hcover
  intro i
  change M.val.map (homOfLE (hUV i)).op _ = M.val.map (homOfLE (hUV i)).op _
  rw [← freeOpenEquiv_naturality, ← freeOpenEquiv_naturality]
  exact congrArg (freeOpenEquiv R M (U i)) (hfg i)

theorem lift_of_ext_one_zero (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) (U : Opens X)
    (hzero : ∀ x : Ext.{u+1} (freeOpen R U) S.X₁ 1, x = 0)
    (s : freeOpen R U ⟶ S.X₃) : ∃ t : freeOpen R U ⟶ S.X₂, t ≫ S.g = s := by
  obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₃ (freeOpen R U) hS (Ext.mk₀ s)
    (n₁ := 1) rfl (hzero _)
  obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective _ _).surjective t
  refine ⟨t, ?_⟩
  apply (Ext.mk₀_bijective _ _).injective
  simpa only [Ext.mk₀_comp_mk₀] using ht

def IsCocycle {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)
    (c : ∀ i j, freeOpen R (U i ⊓ U j) ⟶ M) : Prop :=
  ∀ i j k,
    restrictHom R (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left) (c i j) +
      restrictHom R (show (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k from
        le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c j k) =
    restrictHom R (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right) (c i k)

def HasPrimitives {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R) : Prop :=
  ∀ c : ∀ i j, freeOpen R (U i ⊓ U j) ⟶ M, IsCocycle R U M c →
    ∃ b : ∀ i, freeOpen R (U i) ⟶ M, ∀ i j,
      c i j = restrictHom R inf_le_right (b j) - restrictHom R inf_le_left (b i)

theorem shortExact_lift_of_primitives {J : Type u} (U : J → Opens X) (V : Opens X)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (hzero : ∀ i (x : Ext.{u+1} (freeOpen R (U i)) S.X₁ 1), x = 0)
    (hprimitive : HasPrimitives R U S.X₁) (f : freeOpen R V ⟶ S.X₃) :
    ∃ g : freeOpen R V ⟶ S.X₂, g ≫ S.g = f := by
  classical
  let : Mono S.f := hS.mono_f
  choose t ht using fun i =>
    lift_of_ext_one_zero R S hS (U i) (hzero i) (restrictHom R (hUV i) f)
  have hdiff (i j : J) :
      (restrictHom R inf_le_right (t j) - restrictHom R inf_le_left (t i)) ≫ S.g = 0 := by
    rw [Preadditive.sub_comp, ← restrictHom_comp, ← restrictHom_comp, ht j, ht i,
      restrictHom_restrictHom, restrictHom_restrictHom, sub_self]
  let c (i j : J) : freeOpen R (U i ⊓ U j) ⟶ S.X₁ :=
    hS.exact.lift _ (hdiff i j)
  have hc (i j : J) : c i j ≫ S.f =
      restrictHom R inf_le_right (t j) - restrictHom R inf_le_left (t i) :=
    hS.exact.lift_f _ (hdiff i j)
  have hcoc : IsCocycle R U S.X₁ c := by
    intro i j k
    apply (cancel_mono S.f).mp
    simp only [Preadditive.add_comp, ← restrictHom_comp, hc,
      restrictHom_sub, restrictHom_restrictHom]
    abel
  obtain ⟨b, hb⟩ := hprimitive c hcoc
  let t' (i : J) : freeOpen R (U i) ⟶ S.X₂ := t i - b i ≫ S.f
  have hcompat (i j : J) : restrictHom R inf_le_left (t' i) =
      restrictHom R inf_le_right (t' j) := by
    have hh := hc i j
    rw [hb i j, Preadditive.sub_comp] at hh
    change restrictHom R inf_le_left (t i - b i ≫ S.f) =
      restrictHom R inf_le_right (t j - b j ≫ S.f)
    simp only [restrictHom_sub, restrictHom_comp]
    apply sub_eq_sub_iff_add_eq_add.mpr
    have hh' := sub_eq_sub_iff_add_eq_add.mp hh
    simpa only [add_comm] using hh'
  obtain ⟨g, hg⟩ := hom_glue R U V hUV hcover S.X₂ t' hcompat
  refine ⟨g, ?_⟩
  apply hom_ext R U V hUV hcover S.X₃
  intro i
  rw [restrictHom_comp]
  change (freeOpenMap R (homOfLE (hUV i)) ≫ g) ≫ S.g = _
  rw [hg i]
  change (t i - b i ≫ S.f) ≫ S.g = _
  rw [Preadditive.sub_comp, Category.assoc, S.zero, comp_zero, sub_zero, ht i]

theorem ext_one_eq_zero_of_primitives {J : Type u} (U : J → Opens X) (V : Opens X)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (M : SheafOfModules.{u} R)
    (hzero : ∀ i (x : Ext.{u+1} (freeOpen R (U i)) M 1), x = 0)
    (hprimitive : HasPrimitives R U M)
    (x : Ext.{u+1} (freeOpen R V) M 1) : x = 0 := by
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (freeOpen R V) hS x
    (Ext.eq_zero_of_injective _) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  obtain ⟨g, rfl⟩ := shortExact_lift_of_primitives R U V hUV hcover S hS hzero hprimitive f
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass, Ext.comp_zero] at hy
  exact hy.symm

end
end PiExponent.GeometrySupport.CechOne

end OAI
