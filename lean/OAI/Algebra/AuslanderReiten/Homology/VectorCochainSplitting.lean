import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace OAI

noncomputable section

namespace ArExplicit.VectorCochain

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable (k : Type u) [Field k]

instance vectorSpaceInjective (M : ModuleCat.{u} k) : CategoryTheory.Injective M where
  factors g f hf := by
    obtain ⟨r, hr⟩ := f.hom.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective f).mp hf))
    refine ⟨ModuleCat.ofHom (g.hom.comp r), ?_⟩
    apply ModuleCat.hom_ext
    change (g.hom.comp r).comp f.hom = g.hom
    rw [LinearMap.comp_assoc, hr, LinearMap.comp_id]

abbrev zeroDifferential (X : ℕ → ModuleCat.{u} k) : CochainComplex (ModuleCat.{u} k) ℕ where
  X := X
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

def zeroHomologyIso (X : ℕ → ModuleCat.{u} k) (n : ℕ) :
    (zeroDifferential k X).homology n ≅ X n :=
  ((zeroDifferential k X).isoHomologyπ ((ComplexShape.up ℕ).prev n) n rfl rfl).symm ≪≫
    (zeroDifferential k X).iCyclesIso n ((ComplexShape.up ℕ).next n) rfl rfl

@[simp, reassoc] theorem zeroHomologyIso_π (X : ℕ → ModuleCat.{u} k) (n : ℕ) :
    (zeroDifferential k X).homologyπ n ≫ (zeroHomologyIso k X n).hom =
      (zeroDifferential k X).iCycles n := by
  let a := (zeroDifferential k X).isoHomologyπ ((ComplexShape.up ℕ).prev n) n rfl rfl
  let b := (zeroDifferential k X).iCyclesIso n ((ComplexShape.up ℕ).next n) rfl rfl
  change a.hom ≫ a.inv ≫ b.hom = b.hom
  exact a.hom_inv_id_assoc _

variable (P : CochainComplex (ModuleCat.{u} k) ℕ)

abbrev gradedHomology : CochainComplex (ModuleCat.{u} k) ℕ :=
  zeroDifferential k (fun n => P.homology n)

def cycleSection (n : ℕ) : P.homology n ⟶ P.cycles n :=
  Projective.factorThru (𝟙 (P.homology n)) (P.homologyπ n)

@[simp, reassoc] theorem cycleSection_π (n : ℕ) :
    cycleSection k P n ≫ P.homologyπ n = 𝟙 _ :=
  Projective.factorThru_comp _ _

def representatives : gradedHomology k P ⟶ P where
  f n := cycleSection k P n ≫ P.iCycles n
  comm' i j _ := by simp [gradedHomology, zeroDifferential]

theorem cyclesMap_representatives (n : ℕ) :
    cyclesMap (representatives k P) n =
      (gradedHomology k P).iCycles n ≫ cycleSection k P n := by
  apply (cancel_mono (P.iCycles n)).1
  simp [representatives, Category.assoc]

theorem homologyMap_representatives (n : ℕ) :
    homologyMap (representatives k P) n = (zeroHomologyIso k (fun n => P.homology n) n).hom := by
  apply (cancel_epi ((gradedHomology k P).homologyπ n)).1
  rw [homologyπ_naturality, cyclesMap_representatives, Category.assoc,
    cycleSection_π, Category.comp_id, zeroHomologyIso_π]

instance representatives_quasiIso : QuasiIso (representatives k P) := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, homologyMap_representatives]
  infer_instance

def splitting : HomotopyEquiv (gradedHomology k P) P :=
  Classical.choose ((CochainComplex.quasiIso_iff_of_injective (representatives k P)).mp
    (representatives_quasiIso k P))

@[simp] theorem splitting_hom : (splitting k P).hom = representatives k P :=
  Classical.choose_spec ((CochainComplex.quasiIso_iff_of_injective (representatives k P)).mp
    (representatives_quasiIso k P))

end ArExplicit.VectorCochain

end

end OAI
