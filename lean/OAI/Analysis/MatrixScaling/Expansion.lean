import OAI.Analysis.MatrixScaling.Canonical
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Prod

namespace OAI

/-! Intrinsic and finite-block expansion inequalities. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace Kaplansky
variable {n d r : ℕ} {E F D R : Type*}
variable [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
variable [AddCommGroup D] [Module ℂ D] [AddCommGroup R] [Module ℂ R]

def IntrinsicExpanding (T : Fin n → E →ₗ[ℂ] F) : Prop :=
  ∀ S : Submodule ℂ E, 2 * Module.finrank ℂ S ≤
    Module.finrank ℂ (⨆ i, S.map (T i) : Submodule ℂ F)

theorem intrinsicExpanding_equiv (T : Fin n → E →ₗ[ℂ] F)
    (e : E ≃ₗ[ℂ] D) (f : F ≃ₗ[ℂ] R) (hT : IntrinsicExpanding T) :
    IntrinsicExpanding (fun i => f.toLinearMap.comp ((T i).comp e.symm.toLinearMap)) := by
  intro S
  have h := hT (S.map e.symm.toLinearMap)
  rw [e.symm.finrank_map_eq] at h
  have he : (⨆ i, S.map (f.toLinearMap.comp ((T i).comp e.symm.toLinearMap)) : Submodule ℂ R) =
      (⨆ i, (S.map e.symm.toLinearMap).map (T i) : Submodule ℂ F).map f.toLinearMap := by
    rw [Submodule.map_iSup]
    apply iSup_congr
    intro i
    rw [Submodule.map_comp, Submodule.map_comp]
  rw [he, f.finrank_map_eq]
  exact h

theorem basis_matrix_action (b : Module.Basis (Fin d) ℂ E) (c : Module.Basis (Fin r) ℂ F)
    (T : E →ₗ[ℂ] F) :
    (LinearMap.toMatrix b c T).mulVecLin =
      c.equivFun.toLinearMap.comp (T.comp b.equivFun.symm.toLinearMap) := by
  apply LinearMap.ext
  intro x
  have he := LinearMap.toMatrix_mulVec_repr b c T (b.equivFun.symm x)
  change (LinearMap.toMatrix b c T) *ᵥ b.equivFun (b.equivFun.symm x) =
    c.equivFun (T (b.equivFun.symm x)) at he
  rw [LinearEquiv.apply_symm_apply] at he
  exact he

theorem expanding_in_basis (T : Fin n → E →ₗ[ℂ] F)
    (b : Module.Basis (Fin d) ℂ E) (c : Module.Basis (Fin r) ℂ F)
    (hT : IntrinsicExpanding T) : Expanding (fun i => LinearMap.toMatrix b c (T i)) := by
  have h := intrinsicExpanding_equiv T b.equivFun c.equivFun hT
  have he : (fun i => (LinearMap.toMatrix b c (T i)).mulVecLin) =
      (fun i => c.equivFun.toLinearMap.comp ((T i).comp b.equivFun.symm.toLinearMap)) :=
    funext (fun i => basis_matrix_action b c (T i))
  change IntrinsicExpanding (fun i => (LinearMap.toMatrix b c (T i)).mulVecLin)
  rw [he]
  exact h

end Kaplansky

end

noncomputable section
open scoped BigOperators
open LinearMap
namespace Kaplansky
variable {n : ℕ} {E F G H : Type*}
variable [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
variable [AddCommGroup G] [Module ℂ G] [AddCommGroup H] [Module ℂ H]

/-- The kernel of the last-block projection is the first-block intersection. -/
def prodSubmoduleKernelEquiv (S : Submodule ℂ (E × F)) :
    S.comap (LinearMap.inl ℂ E F) ≃ₗ[ℂ]
      LinearMap.ker ((LinearMap.snd ℂ E F).comp S.subtype) where
  toFun x := ⟨⟨(x.val,0),x.property⟩,rfl⟩
  invFun x := ⟨x.val.val.1, by
    have hz : x.val.val.2 = 0 := x.property
    change (x.val.val.1,0) ∈ S
    rw [← hz]
    exact x.val.property⟩
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact x.property.symm
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_smul' z x := by
    apply Subtype.ext
    apply Subtype.ext
    simp

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

theorem prod_submodule_finrank (S : Submodule ℂ (E × F)) :
    Module.finrank ℂ (S.comap (LinearMap.inl ℂ E F)) +
      Module.finrank ℂ (S.map (LinearMap.snd ℂ E F)) = Module.finrank ℂ S := by
  have h := LinearMap.finrank_range_add_finrank_ker ((LinearMap.snd ℂ E F).comp S.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype] at h
  rw [← (prodSubmoduleKernelEquiv S).finrank_eq] at h
  omega

/-- Expansion restricted to the dimensions used by the sixteen small-subspace maps. -/
def ExpandingThrough (m : ℕ) (T : Fin n → E →ₗ[ℂ] G) : Prop :=
  ∀ S : Submodule ℂ E, Module.finrank ℂ S ≤ m →
    2 * Module.finrank ℂ S ≤ Module.finrank ℂ (⨆ i, S.map (T i) : Submodule ℂ G)

variable [FiniteDimensional ℂ G] [FiniteDimensional ℂ H]

theorem expandingThrough_prod (m : ℕ) (T : Fin n → E →ₗ[ℂ] G) (U : Fin n → F →ₗ[ℂ] H)
    (hT : ExpandingThrough m T) (hU : ExpandingThrough m U) :
    ExpandingThrough m (fun i => (T i).prodMap (U i)) := by
  intro S hS
  let W : Submodule ℂ (G × H) := ⨆ i, S.map ((T i).prodMap (U i))
  let L := S.comap (LinearMap.inl ℂ E F)
  let R := S.map (LinearMap.snd ℂ E F)
  have hdim := prod_submodule_finrank S
  have hL := hT L (by dsimp [L]; omega)
  have hR := hU R (by dsimp [R]; omega)
  have hright : W.map (LinearMap.snd ℂ G H) =
      ⨆ i, R.map (U i) := by
    dsimp [W,R]
    rw [Submodule.map_iSup]
    apply iSup_congr
    intro i
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
  have hleft : (⨆ i, L.map (T i) : Submodule ℂ G) ≤ W.comap (LinearMap.inl ℂ G H) := by
    apply iSup_le
    intro i
    rintro _ ⟨v,hv,rfl⟩
    change (T i v,0) ∈ W
    apply (le_iSup (fun j => S.map ((T j).prodMap (U j))) i)
    refine ⟨(v,0),hv,?_⟩
    simp
  have hw := prod_submodule_finrank W
  have hlrank := Submodule.finrank_mono hleft
  rw [hright] at hw
  change 2 * Module.finrank ℂ S ≤ Module.finrank ℂ W
  dsimp [L,R] at hL hR hlrank hw
  omega

end Kaplansky

end

noncomputable section
namespace Kaplansky
variable {n : ℕ}

theorem expandingThrough_equiv {E F D R : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup D] [Module ℂ D] [AddCommGroup R] [Module ℂ R]
    (m : ℕ) (T : Fin n → E →ₗ[ℂ] F) (e : E ≃ₗ[ℂ] D) (f : F ≃ₗ[ℂ] R)
    (hT : ExpandingThrough m T) :
    ExpandingThrough m (fun i => f.toLinearMap.comp ((T i).comp e.symm.toLinearMap)) := by
  intro S hS
  have h := hT (S.map e.symm.toLinearMap) (by simpa only [e.symm.finrank_map_eq] using hS)
  rw [e.symm.finrank_map_eq] at h
  have he : (⨆ i, S.map (f.toLinearMap.comp ((T i).comp e.symm.toLinearMap)) : Submodule ℂ R) =
      (⨆ i, (S.map e.symm.toLinearMap).map (T i) : Submodule ℂ F).map f.toLinearMap := by
    rw [Submodule.map_iSup]
    apply iSup_congr
    intro i
    rw [Submodule.map_comp, Submodule.map_comp]
  rw [he, f.finrank_map_eq]
  exact h

def piSuccLinearEquiv {k : ℕ} (E : Fin (k+1) → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)] :
    (∀ j, E j) ≃ₗ[ℂ] E 0 × (∀ j : Fin k, E j.succ) where
  toFun v := (v 0,fun j => v j.succ)
  invFun v := Fin.cases v.1 v.2
  left_inv v := by funext j; refine Fin.cases ?_ (fun i => ?_) j <;> rfl
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def blockDiagonal {k : ℕ} {E : Fin k → Type*} {F : Fin k → Type*}
    [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)]
    [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)]
    (T : ∀ j, Fin n → E j →ₗ[ℂ] F j) (i : Fin n) : (∀ j, E j) →ₗ[ℂ] (∀ j, F j) where
  toFun v j := T j i (v j)
  map_add' v w := by funext j; exact map_add (T j i) _ _
  map_smul' z v := by funext j; exact map_smul (T j i) _ _

theorem expandingThrough_blocks (k m : ℕ)
    (E : Fin k → Type*) (F : Fin k → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)] [∀ j, FiniteDimensional ℂ (E j)]
    [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] [∀ j, FiniteDimensional ℂ (F j)]
    (T : ∀ j, Fin n → E j →ₗ[ℂ] F j) (hT : ∀ j, ExpandingThrough m (T j)) :
    ExpandingThrough m (blockDiagonal T) := by
  induction k with
  | zero =>
      intro S _
      have hz : Module.finrank ℂ S = 0 := Module.finrank_zero_of_subsingleton
      simp [hz]
  | succ k ih =>
      have ht := ih (fun j => E j.succ) (fun j => F j.succ)
        (fun j => T j.succ) (fun j => hT j.succ)
      have hp := expandingThrough_prod m (T 0) (blockDiagonal (fun j : Fin k => T j.succ)) (hT 0) ht
      have he := expandingThrough_equiv m _ (piSuccLinearEquiv E).symm (piSuccLinearEquiv F).symm hp
      convert he using 1
      funext i
      apply LinearMap.ext
      intro v
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> rfl

end Kaplansky

end

noncomputable section
namespace Kaplansky
variable {E F G H : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
  [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ H]

theorem image_iSup_finrank_le {n N : ℕ} (T : Fin n → E →ₗ[ℂ] F)
    (U : Fin N → E →ₗ[ℂ] H) (f : F →ₗ[ℂ] H) (hf : Function.Injective f)
    (a : Fin n → Fin N) (ha : ∀ i, U (a i)=f.comp (T i)) (S : Submodule ℂ E) :
    Module.finrank ℂ (⨆ i, S.map (T i) : Submodule ℂ F) ≤ Module.finrank ℂ (⨆ i, S.map (U i) : Submodule ℂ H) := by
  have he := (Submodule.equivMapOfInjective f hf (⨆ i, S.map (T i) : Submodule ℂ F)).finrank_eq
  rw [he]
  apply Submodule.finrank_mono
  rw [Submodule.map_iSup]
  apply iSup_le
  intro i
  rw [← Submodule.map_comp,← ha i]
  exact le_iSup (fun q : Fin N => S.map (U q)) (a i)

theorem combined_expanding (m : ℕ) (A : Fin 16 → E →ₗ[ℂ] F)
    (B : Fin 8 → E →ₗ[ℂ] G) (f : F →ₗ[ℂ] H) (g : G →ₗ[ℂ] H)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hA : ExpandingThrough m A)
    (hB : ∀ S : Submodule ℂ E, m<Module.finrank ℂ S →
      2*Module.finrank ℂ S≤Module.finrank ℂ (⨆ i, S.map (B i) : Submodule ℂ G)) :
    IntrinsicExpanding (Fin.addCases (fun i => f.comp (A i)) (fun i => g.comp (B i))) := by
  intro S
  by_cases hs : Module.finrank ℂ S≤m
  · exact (hA S hs).trans (image_iSup_finrank_le A _ f hf (Fin.castAdd 8) (by intro i; simp) S)
  · exact (hB S (by omega)).trans (image_iSup_finrank_le B _ g hg (Fin.natAdd 16) (by intro i; simp) S)

end Kaplansky

end

end OAI
