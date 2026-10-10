import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHomComplex
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionExtZero
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

abbrev homShort (n : ℕ) := (homCochain k R P.complex Y).sc' (n-1) n (n+1)

theorem homShort_outgoing (n : ℕ) :
    (homShort k R (Y := Y) P n).g =
      ModuleCat.ofHom (LinearMap.lcomp k Y (P.complex.d (n+1) n).hom) :=
  homCochain_d k R P.complex Y n

theorem homShort_incoming_succ (n : ℕ) :
    (homShort k R (Y := Y) P (n+1)).f =
      ModuleCat.ofHom (LinearMap.lcomp k Y (P.complex.d (n+1) n).hom) := by
  exact homCochain_d k R P.complex Y n

theorem homShort_incoming_zero : (homShort k R (Y := Y) P 0).f = 0 := by
  exact (homCochain k R P.complex Y).shape 0 0 (by simp)

theorem homCycle_closed (n : ℕ) (f : LinearMap.ker (homShort k R (Y := Y) P n).g.hom) :
    P.complex.d (n+1) n ≫ ModuleCat.ofHom (X := P.complex.X n) (Y := Y) f.val = 0 := by
  apply ModuleCat.hom_ext
  let g : P.complex.X n →ₗ[R] Y := f.val
  have hf : (homShort k R (Y := Y) P n).g.hom g = 0 := f.property
  rw [homShort_outgoing] at hf
  exact hf

def homCyclesToExt (n : ℕ) :
    LinearMap.ker (homShort k R (Y := Y) P n).g.hom →ₗ[k] Ext X Y n where
  toFun f := P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) f.val)
    (n+1) rfl (homCycle_closed k R P n f)
  map_add' f g := (P.add_extMk
    (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) f.val)
    (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) g.val) (n+1) rfl
      (homCycle_closed k R P n f) (homCycle_closed k R P n g)).symm
  map_smul' a f := ResolutionHomology.extMk_smul P n
    (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) f.val) (homCycle_closed k R P n f) a

theorem homCyclesToExt_surjective (n : ℕ) :
    Function.Surjective (homCyclesToExt k R (Y := Y) P n) := by
  intro a
  obtain ⟨f, hf, hfa⟩ := P.extMk_surjective a (n+1) rfl
  refine ⟨⟨f.hom, ?_⟩, hfa⟩
  change (homShort k R (Y := Y) P n).g.hom f.hom = 0
  rw [homShort_outgoing]
  exact congrArg ModuleCat.Hom.hom hf

theorem homCyclesToExt_kernel (n : ℕ) :
    LinearMap.ker (homCyclesToExt k R (Y := Y) P n) =
      LinearMap.range (homShort k R (Y := Y) P n).moduleCatToCycles := by
  ext x
  cases n with
  | zero =>
    constructor
    · intro hx
      have hx0 : ModuleCat.ofHom x.val = 0 :=
        (ResolutionHomology.extMk_zeroDegree_eq_zero_iff P _ (homCycle_closed k R P 0 x)).mp hx
      refine ⟨0, Subtype.ext ?_⟩
      change (0 : P.complex.X 0 →ₗ[R] Y) = x.val
      exact (congrArg ModuleCat.Hom.hom hx0).symm
    · rintro ⟨f, rfl⟩
      have hf0 : (homShort k R (Y := Y) P 0).moduleCatToCycles f = 0 := by
        apply Subtype.ext
        change (homShort k R (Y := Y) P 0).f.hom f = 0
        rw [homShort_incoming_zero]
        rfl
      rw [hf0]
      exact map_zero _
  | succ n =>
    constructor
    · intro hx
      obtain ⟨f, hf⟩ := (P.extMk_eq_zero_iff (ModuleCat.ofHom x.val)
        (n+2) rfl (homCycle_closed k R P (n+1) x) n rfl).mp hx
      refine ⟨f.hom, Subtype.ext ?_⟩
      change (homShort k R (Y := Y) P (n+1)).f.hom f.hom = x.val
      rw [homShort_incoming_succ]
      exact congrArg ModuleCat.Hom.hom hf
    · rintro ⟨f, rfl⟩
      apply (P.extMk_eq_zero_iff _ (n+2) rfl
        (homCycle_closed k R P (n+1) ((homShort k R (Y := Y) P (n+1)).moduleCatToCycles f)) n rfl).mpr
      refine ⟨ModuleCat.ofHom f, ?_⟩
      apply ModuleCat.hom_ext
      change f.comp (P.complex.d (n+1) n).hom =
        (homShort k R (Y := Y) P (n+1)).f.hom f
      rw [homShort_incoming_succ]
      rfl

def homShortExtEquiv (n : ℕ) :
    (homShort k R (Y := Y) P n).homology ≃ₗ[k] Ext X Y n :=
  (homShort k R (Y := Y) P n).moduleCatHomologyIso.toLinearEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (homCyclesToExt_kernel k R P n).symm).trans
      ((homCyclesToExt k R P n).quotKerEquivOfSurjective
        (homCyclesToExt_surjective k R P n)))

def homCochainExtEquiv (n : ℕ) :
    (homCochain k R P.complex Y).homology n ≃ₗ[k] Ext X Y n :=
  ((homCochain k R P.complex Y).homologyIsoSc' (n-1) n (n+1)
    (by cases n <;> simp) (by simp)).toLinearEquiv.trans (homShortExtEquiv k R P n)

end ArExplicit.ExternalTensor

end

end OAI
