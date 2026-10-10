import OAI.Algebra.AuslanderReiten.Duality.LinearHomologyDuality
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit.ResolutionHomology
universe u v w
variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
variable {X Y : C} (P : ProjectiveResolution X)

def differential (n : ℕ) : (P.complex.X n ⟶ Y) →ₗ[k] (P.complex.X (n + 1) ⟶ Y) where
  toFun f := P.complex.d (n + 1) n ≫ f
  map_add' f g := by simp only [Preadditive.comp_add]
  map_smul' a f := by simp only [Linear.comp_smul, RingHom.id_apply]

@[simp] theorem differential_apply (n : ℕ) (f : P.complex.X n ⟶ Y) :
    differential (k := k) P n f = P.complex.d (n + 1) n ≫ f := rfl

theorem differential_comp (n : ℕ) :
    (differential (k := k) (Y := Y) P (n + 1)).comp (differential P n) = 0 := by
  ext f
  change P.complex.d (n + 2) (n + 1) ≫ (P.complex.d (n + 1) n ≫ f) = 0
  rw [← Category.assoc, P.complex.d_comp_d, Limits.zero_comp]

variable [HasExt.{w} C]

theorem extMk_smul (n : ℕ) (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n + 1) n ≫ f = 0) (a : k) :
    P.extMk (a • f) (n + 1) rfl (by simp [hf]) = a • P.extMk f (n + 1) rfl hf := by
  rw [Ext.smul_eq_comp_mk₀, P.extMk_comp_mk₀]
  congr 1
  simp

def cyclesToExt (n : ℕ) :
    LinearMap.ker (differential (k := k) (Y := Y) P (n + 1)) →ₗ[k] Ext X Y (n + 1) where
  toFun f := P.extMk f.val (n + 2) rfl f.property
  map_add' f g := (P.add_extMk f.val g.val _ rfl f.property g.property).symm
  map_smul' a f := extMk_smul P (n + 1) f.val f.property a

theorem cyclesToExt_surjective (n : ℕ) :
    Function.Surjective (cyclesToExt (k := k) (Y := Y) P n) := by
  intro a
  obtain ⟨f, hf, hfa⟩ := P.extMk_surjective a (n + 2) rfl
  exact ⟨⟨f, hf⟩, hfa⟩

theorem cyclesToExt_kernel (n : ℕ) :
    LinearMap.ker (cyclesToExt (k := k) (Y := Y) P n) =
      LinearHomology.boundaries (differential P n) (differential P (n + 1)) (differential_comp P n) := by
  ext x
  constructor
  · intro hx
    obtain ⟨f, hf⟩ := (P.extMk_eq_zero_iff x.val (n + 2) rfl x.property n rfl).mp hx
    exact ⟨f, Subtype.ext hf⟩
  · rintro ⟨f, hfx⟩
    apply (P.extMk_eq_zero_iff x.val (n + 2) rfl x.property n rfl).mpr
    exact ⟨f, congrArg Subtype.val hfx⟩

def extEquiv (n : ℕ) :
    LinearHomology.Homology (differential (k := k) (Y := Y) P n)
      (differential P (n + 1)) (differential_comp P n) ≃ₗ[k] Ext X Y (n + 1) :=
  (Submodule.quotEquivOfEq _ _ (cyclesToExt_kernel P n).symm).trans
    ((cyclesToExt P n).quotKerEquivOfSurjective (cyclesToExt_surjective P n))

end ArExplicit.ResolutionHomology

end

end OAI
