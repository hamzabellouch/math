import Mathlib
import OAI.GroupTheory.FiniteType.SingularChains

namespace OAI

noncomputable section
namespace ProductFiniteResolution

open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra

variable {k G : Type} [CommRing k] [Group G]

def repMap {C D : Rep k G} (f : C.ρ.asModule →ₗ[k[G]] D.ρ.asModule) : C ⟶ D :=
  Rep.ofHom ((IntertwiningMap.equivLinearMapAsModule C.ρ D.ρ).symm f)

@[simp] lemma moduleMap_repMap {C D : Rep k G}
    (f : C.ρ.asModule →ₗ[k[G]] D.ρ.asModule) :
    ProductCriterion.moduleMap (repMap f) = f :=
  (IntertwiningMap.equivLinearMapAsModule C.ρ D.ρ).apply_symm_apply f

@[simp] lemma repMap_moduleMap {C D : Rep k G} (f : C ⟶ D) :
    repMap (ProductCriterion.moduleMap f) = f := by
  apply Rep.hom_injective
  exact (IntertwiningMap.equivLinearMapAsModule C.ρ D.ρ).symm_apply_apply f.hom

def fromGenerators {α : Type} (C : Rep k G) (s : α → C.ρ.asModule) :
    Rep.free k G α ⟶ C :=
  repMap ((Representation.freeAsModuleBasis k G α).constr k s)

lemma fromGenerators_surjective {α : Type} (C : Rep k G)
    (s : α → C.ρ.asModule) (hs : Submodule.span k[G] (Set.range s) = ⊤) :
    Function.Surjective (fromGenerators C s).hom := by
  have hr : LinearMap.range (ProductCriterion.moduleMap (fromGenerators C s)) = ⊤ := by
    rw [fromGenerators, moduleMap_repMap, Module.Basis.constr_range, hs]
  have h := LinearMap.range_eq_top.mp hr
  intro x
  obtain ⟨y, hy⟩ := h (C.ρ.asModuleEquiv.symm x)
  exact ⟨(Rep.free k G α).ρ.asModuleEquiv y, congrArg C.ρ.asModuleEquiv hy⟩

structure FreeCover (C : Rep k G) where
  ι : Type
  π : Rep.free k G ι ⟶ C
  surjective : Function.Surjective π.hom
  finite_of : Module.Finite k[G] C.ρ.asModule → Finite ι

noncomputable def freeCover (C : Rep k G) : FreeCover C := by
  classical
  by_cases h : Module.Finite k[G] C.ρ.asModule
  · letI := h
    let n := Classical.choose (Module.Finite.exists_fin (R := k[G]) (M := C.ρ.asModule))
    have hn := Classical.choose_spec (Module.Finite.exists_fin (R := k[G]) (M := C.ρ.asModule))
    let s := Classical.choose hn
    have hs := Classical.choose_spec hn
    exact ⟨Fin n, fromGenerators C s, fromGenerators_surjective C s hs,
      fun _ => inferInstance⟩
  · exact ⟨C.ρ.asModule, fromGenerators C id,
      fromGenerators_surjective C id (by simp), fun hf => False.elim (h hf)⟩

abbrev cover (C : Rep k G) : Rep k G := Rep.free k G (freeCover C).ι
abbrev coverπ (C : Rep k G) : cover C ⟶ C := (freeCover C).π

instance coverπ_epi (C : Rep k G) : Epi (coverπ C) :=
  (Rep.epi_iff_surjective _).mpr (freeCover C).surjective

instance cover_projective (C : Rep k G) : Projective (cover C) := by
  dsimp [cover]
  infer_instance

abbrev kerRep {C D : Rep k G} (f : C ⟶ D) : Rep k G :=
  Rep.of f.hom.ker.toRepresentation

def kerι {C D : Rep k G} (f : C ⟶ D) : kerRep f ⟶ C :=
  Rep.ofHom ⟨f.hom.ker.toSubmodule.subtype, fun _ => rfl⟩

@[simp] lemma kerι_apply {C D : Rep k G} (f : C ⟶ D) (x : kerRep f) :
    (kerι f).hom x = x.val := rfl

@[reassoc (attr := simp)] lemma kerι_comp {C D : Rep k G} (f : C ⟶ D) :
    kerι f ≫ f = 0 := by
  ext x
  exact x.property

def kerAsModuleEquiv {C D : Rep k G} (f : C ⟶ D) :
    (kerRep f).ρ.asModule ≃ₗ[k[G]] (ProductCriterion.moduleMap f).ker :=
  LinearEquiv.ofBijective
    ((ProductCriterion.moduleMap (kerι f)).codRestrict _ (fun x => by
      change ProductCriterion.moduleMap f (ProductCriterion.moduleMap (kerι f) x) = 0
      exact congrArg D.ρ.asModuleEquiv.symm ((kerRep f).ρ.asModuleEquiv x).property))
    (by
      constructor
      · intro x y h
        apply (kerRep f).ρ.asModuleEquiv.injective
        apply Subtype.ext
        exact congrArg C.ρ.asModuleEquiv (Subtype.ext_iff.mp h)
      · intro y
        refine ⟨(kerRep f).ρ.asModuleEquiv.symm
          ⟨C.ρ.asModuleEquiv y.val, ?_⟩, ?_⟩
        · exact congrArg D.ρ.asModuleEquiv y.property
        · apply Subtype.ext
          rfl)

lemma kerRep_finite {C D : Rep k G} (f : C ⟶ D)
    (h : (ProductCriterion.moduleMap f).ker.FG) : Module.Finite k[G] (kerRep f).ρ.asModule := by
  let := Module.Finite.iff_fg.mpr h
  exact Module.Finite.equiv (kerAsModuleEquiv f).symm

abbrev next {C D : Rep k G} (f : C ⟶ D) := cover (kerRep f)

def differential {C D : Rep k G} (f : C ⟶ D) : next f ⟶ C :=
  coverπ (kerRep f) ≫ kerι f

@[reassoc (attr := simp)] lemma differential_comp {C D : Rep k G} (f : C ⟶ D) :
    differential f ≫ f = 0 := by simp [differential]

lemma differential_exact {C D : Rep k G} (f : C ⟶ D) :
    (ShortComplex.mk (differential f) f (differential_comp f)).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, hy⟩ := (freeCover (kerRep f)).surjective ⟨x, hx⟩
  refine ⟨y, ?_⟩
  exact congrArg Subtype.val hy

structure Beginning (Z : Rep k G) where
  α₀ : Type
  α₁ : Type
  α₂ : Type
  [finite₀ : Finite α₀]
  [finite₁ : Finite α₁]
  [finite₂ : Finite α₂]
  d₁ : Rep.free k G α₁ ⟶ Rep.free k G α₀
  d₂ : Rep.free k G α₂ ⟶ Rep.free k G α₁
  ε : Rep.free k G α₀ ⟶ Z
  d₂_d₁ : d₂ ≫ d₁ = 0
  d₁_ε : d₁ ≫ ε = 0
  exact₁ : (ShortComplex.mk d₂ d₁ d₂_d₁).Exact
  exact₀ : (ShortComplex.mk d₁ ε d₁_ε).Exact
  [epi_ε : Epi ε]

attribute [instance] Beginning.finite₀ Beginning.finite₁ Beginning.finite₂ Beginning.epi_ε

variable {Z : Rep k G} (B : Beginning Z)

def extendedComplex : ChainComplex (Rep k G) ℕ :=
  ChainComplex.mk (Rep.free k G B.α₀) (Rep.free k G B.α₁) (Rep.free k G B.α₂)
    B.d₁ B.d₂ B.d₂_d₁ (fun S => ⟨next S.f, differential S.f, differential_comp S.f⟩)

@[simp] lemma extendedComplex_d_1_0 : (extendedComplex B).d 1 0 = B.d₁ := by
  simp [extendedComplex]

@[simp] lemma extendedComplex_d_2_1 : (extendedComplex B).d 2 1 = B.d₂ := by
  simp [extendedComplex]

lemma extendedComplex_exactAt_succ (n : ℕ) : (extendedComplex B).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  change (ShortComplex.mk _ _ ((extendedComplex B).d_comp_d (n + 2) (n + 1) n)).Exact
  erw [← ChainComplex.mkAux_eq_shortComplex_mk_d_comp_d
    (Rep.free k G B.α₀) (Rep.free k G B.α₁) (Rep.free k G B.α₂)
    B.d₁ B.d₂ B.d₂_d₁
    (fun S => ⟨next S.f, differential S.f, differential_comp S.f⟩) n]
  cases n with
  | zero => exact B.exact₁
  | succ n => exact differential_exact (k := k) (G := G) _

instance extendedComplex_projective (n : ℕ) : Projective ((extendedComplex B).X n) := by
  obtain (_ | _ | _ | n) := n <;> apply Rep.free_projective

def resolution : ProjectiveResolution Z where
  complex := extendedComplex B
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨B.ε, by
    rw [extendedComplex_d_1_0]; exact B.d₁_ε⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨B.exact₀, B.epi_ε⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by
            simp only [Iso.refl_hom, extendedComplex]
            change 𝟙 (Rep.free k G B.α₁) ≫ B.d₁ = B.d₁ ≫ 𝟙 (Rep.free k G B.α₀)
            simp)
          (by
            change 𝟙 (Rep.free k G B.α₀) ≫ B.ε = B.ε ≫ 𝟙 Z
            simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact extendedComplex_exactAt_succ B n
      · apply ChainComplex.exactAt_succ_single_obj⟩

def degreeIndex : ℕ → Type
  | 0 => B.α₀
  | 1 => B.α₁
  | 2 => B.α₂
  | n + 3 => (freeCover (kerRep ((extendedComplex B).d (n + 2) (n + 1)))).ι

lemma degree_eq_free (n : ℕ) : (extendedComplex B).X n = Rep.free k G (degreeIndex B n) := by
  obtain (_ | _ | _ | n) := n
  · rfl
  · rfl
  · rfl
  · change next (ChainComplex.mkAux _ _ _ B.d₁ B.d₂ B.d₂_d₁
        (fun S => ⟨next S.f, differential S.f, differential_comp S.f⟩) n).f =
      next ((extendedComplex B).d (n + 2) (n + 1))
    have h := ChainComplex.mkAux_eq_shortComplex_mk_d_comp_d
      (Rep.free k G B.α₀) (Rep.free k G B.α₁) (Rep.free k G B.α₂)
      B.d₁ B.d₂ B.d₂_d₁
      (fun S : ShortComplex (Rep k G) => ⟨next S.f, differential S.f, differential_comp S.f⟩) n
    change _ = next ((ShortComplex.mk _ _
      ((extendedComplex B).d_comp_d (n + 2) (n + 1) n)).f)
    exact congrArg (fun S : ShortComplex (Rep k G) => next S.f) h

lemma kerRep_finite_of_product_exact {U C D : Rep k G} (f : U ⟶ C) (g : C ⟶ D)
    (hfg : f ≫ g = 0) {α β : Type} [Finite α]
    (eC : C = Rep.free k G α) (eD : D = Rep.free k G β)
    (hex : ∀ I : Type, ((ShortComplex.mk f g hfg).map
      ((Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I))).Exact) :
    Module.Finite k[G] (kerRep g).ρ.asModule := by
  cases eC
  cases eD
  apply kerRep_finite g
  apply ProductCriterion.kernel_fg_of_tensor_homology_zero U f g hfg
  intro I
  exact (ShortComplex.exact_iff_isZero_homology _).mp (hex I)

lemma degreeIndex_finite (B : Beginning (Rep.trivial k G k))
    (hzero : ∀ (I : Type) (n : ℕ), 2 ≤ n →
      IsZero (groupHomology (RegularProductR.rep k G I) n)) (n : ℕ) :
    Finite (degreeIndex B n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain (_ | _ | _ | n) := n
    · exact B.finite₀
    · exact B.finite₁
    · exact B.finite₂
    · have : Finite (degreeIndex B (n + 2)) := ih (n + 2) (by omega)
      apply (freeCover _).finite_of
      apply kerRep_finite_of_product_exact
        ((extendedComplex B).d (n + 3) (n + 2))
        ((extendedComplex B).d (n + 2) (n + 1))
        ((extendedComplex B).d_comp_d _ _ _)
        (degree_eq_free B (n + 2)) (degree_eq_free B (n + 1))
      intro I
      have he := ProductCriterion.product_resolution_exact (resolution B) (n + 2)
        (fun J => hzero J (n + 2) (by omega)) I
      rw [HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1)
        (by simp) (by simp)] at he
      exact he

theorem exists_finite_free_resolution (B : Beginning (Rep.trivial k G k))
    (hzero : ∀ (I : Type) (n : ℕ), 2 ≤ n →
      IsZero (groupHomology (RegularProductR.rep k G I) n)) :
    ∃ P : ProjectiveResolution (Rep.trivial k G k),
      ∀ n, ∃ α : Type, Finite α ∧ Nonempty (P.complex.X n ≅ Rep.free k G α) := by
  refine ⟨resolution B, fun n => ⟨degreeIndex B n, degreeIndex_finite B hzero n, ?_⟩⟩
  exact ⟨eqToIso (degree_eq_free B n)⟩

end ProductFiniteResolution

end

end OAI
