import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u
variable {R : Type u} [Ring R]

def cutSub (K : CochainComplex (ModuleCat.{u} R) ℤ) (a j : ℤ) : Submodule R (K.X j) :=
  if a ≤ j then ⊤ else ⊥

lemma mem_cutSub {K : CochainComplex (ModuleCat.{u} R) ℤ} {a j : ℤ} {x : K.X j} :
    x ∈ cutSub K a j ↔ a ≤ j ∨ x = 0 := by
  by_cases h : a ≤ j <;> simp [cutSub, h]

lemma cutSub_d {K : CochainComplex (ModuleCat.{u} R) ℤ} {a j k : ℤ}
    {x : K.X j} (hx : x ∈ cutSub K a j) : K.d j k x ∈ cutSub K a k := by
  rw [mem_cutSub] at hx ⊢
  by_cases h : (ComplexShape.up ℤ).Rel j k
  · change j + 1 = k at h
    rcases hx with hx | rfl
    · exact Or.inl (by omega)
    · exact Or.inr (map_zero _)
  · rw [K.shape j k h]
    exact Or.inr rfl

def cut (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    CochainComplex (ModuleCat R) ℤ where
  X j := ModuleCat.of R (cutSub K a j)
  d j k := ModuleCat.ofHom
    { toFun := fun x => ⟨K.d j k x, cutSub_d x.property⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun r x => Subtype.ext (map_smul _ _ _) }
  shape j k hjk := by
    ext x
    change K.d j k x = 0
    rw [K.shape j k hjk]
    rfl
  d_comp_d' j k l hjk hkl := by
    ext x
    exact ConcreteCategory.congr_hom (K.d_comp_d j k l) x

def cutι (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) : cut K a ⟶ K where
  f j := ModuleCat.ofHom (cutSub K a j).subtype
  comm' _ _ _ := rfl

instance cutι_mono (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) : Mono (cutι K a) := by
  apply HomologicalComplex.mono_of_mono_f
  intro j
  exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective

lemma cutSub_le (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : b ≤ a) (j : ℤ) :
    cutSub K a j ≤ cutSub K b j := by
  intro x hx
  rw [mem_cutSub] at hx ⊢
  exact hx.imp (le_trans h) id

def cutMap (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : b ≤ a) :
    cut K a ⟶ cut K b where
  f j := ModuleCat.ofHom (Submodule.inclusion (cutSub_le K h j))
  comm' _ _ _ := rfl

@[reassoc (attr := simp)]
lemma cutMap_ι (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : b ≤ a) :
    cutMap K h ≫ cutι K b = cutι K a := rfl

lemma cut_isZero_X (K : CochainComplex (ModuleCat.{u} R) ℤ) (a j : ℤ) (h : j < a) :
    IsZero ((cut K a).X j) := by
  apply ModuleCat.isZero_iff_subsingleton.2
  have : cutSub K a j = ⊥ := ite_eq_right (by omega)
  change Subsingleton (cutSub K a j)
  rw [this]
  infer_instance

lemma cutι_f_isIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (a j : ℤ) (h : a ≤ j) :
    IsIso ((cutι K a).f j) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨Subtype.val_injective, fun x => ?_⟩
  exact ⟨⟨x, mem_cutSub.mpr (Or.inl h)⟩, rfl⟩

def cutπ (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    cut K a ⟶ (HomologicalComplex.single (ModuleCat R) (ComplexShape.up ℤ) a).obj (K.X a) :=
  mkHomToSingle ((cutι K a).f a) (fun i hi => by
    have h : i < a := by change i + 1 = a at hi; omega
    exact (cut_isZero_X K a i h).eq_of_src _ _)

lemma cutMap_π (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    cutMap K (show a ≤ a+1 by omega) ≫ cutπ K a = 0 := by
  apply to_single_hom_ext
  apply (cut_isZero_X K (a+1) a (by omega)).eq_of_src

instance cutMap_mono (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : b ≤ a) :
    Mono (cutMap K h) := by
  have : Mono (cutMap K h ≫ cutι K b) := by
    rw [cutMap_ι]
    infer_instance
  exact mono_of_mono _ (cutι K b)

instance cutπ_f_self_isIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    IsIso ((cutπ K a).f a) := by
  dsimp only [cutπ]
  rw [mkHomToSingle_f]
  have := cutι_f_isIso K a a (le_refl a)
  infer_instance

instance cutπ_epi (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) : Epi (cutπ K a) := by
  apply HomologicalComplex.epi_of_epi_f
  intro j
  by_cases h : j = a
  · subst j; infer_instance
  · exact (isZero_single_obj_X (ComplexShape.up ℤ) a (K.X a) j h).epi _

def cutShortComplex (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
  ShortComplex.mk (cutMap K (show a ≤ a+1 by omega)) (cutπ K a) (cutMap_π K a)

lemma cut_shortExact (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (cutShortComplex K a).ShortExact where
  exact := by
    apply HomologicalComplex.exact_of_degreewise_exact
    intro j
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change ↥(cutSub K a j) at x
    change (cutπ K a).f j x = 0 at hx
    by_cases h : j = a
    · subst j
      have hi : Function.Injective ((cutπ K a).f a) :=
        (ModuleCat.mono_iff_injective _).1 inferInstance
      have hx' : x = 0 := hi (hx.trans (map_zero _).symm)
      exact ⟨0, by rw [hx']; rfl⟩
    · refine ⟨⟨(x : K.X j), ?_⟩, ?_⟩
      · have hx' := x.property
        rw [mem_cutSub] at hx' ⊢
        exact hx'.imp (fun h' => by omega) id
      · rfl
  mono_f := by change Mono (cutMap K (show a ≤ a+1 by omega)); infer_instance
  epi_g := by change Epi (cutπ K a); infer_instance

end LittleFinitistic.DerivedSupport

end

end OAI
