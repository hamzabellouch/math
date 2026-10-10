import Mathlib

namespace OAI

section
noncomputable section
open Module Function

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

def subspaceRepresentation (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g, W.map (ρ g).toLinearMap=W) : G →* (W ≃ₗ[K] W) where
  toFun g := (ρ g).ofSubmodules W W (hW g)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

def quotientRepresentation (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g, W.map (ρ g).toLinearMap=W) : G →* ((V ⧸ W) ≃ₗ[K] (V ⧸ W)) where
  toFun g := Submodule.Quotient.equiv W W (ρ g) (hW g)
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp
  map_mul' g h := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp

@[simp] lemma subspaceRepresentation_apply (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g, W.map (ρ g).toLinearMap=W) (g : G) (w : W) :
    (subspaceRepresentation ρ W hW g w : V)=ρ g w := rfl

@[simp] lemma quotientRepresentation_apply (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g, W.map (ρ g).toLinearMap=W) (g : G) (v : V) :
    quotientRepresentation ρ W hW g (Submodule.Quotient.mk v)=Submodule.Quotient.mk (ρ g v) := rfl

lemma commute_of_identity_on_subspace_quotient (W : Submodule K V) (e f : V ≃ₗ[K] V)
    (heW : ∀ w∈W, e w=w) (hfW : ∀ w∈W, f w=w)
    (heQ : ∀ v, e v-v∈W) (hfQ : ∀ v, f v-v∈W) : e*f=f*e := by
  ext v
  have he := heW (f v-v) (hfQ v)
  have hf := hfW (e v-v) (heQ v)
  rw [map_sub] at he hf
  change e (f v)=f (e v)
  have h1 : e (f v)=f v-v+e v := (sub_eq_iff_eq_add).mp he
  have h2 : f (e v)=e v-v+f v := (sub_eq_iff_eq_add).mp hf
  rw [h1,h2]
  abel

lemma solvable_of_subspace_quotient (ρ : G →* (V ≃ₗ[K] V)) (hρ : Injective ρ)
    (W : Submodule K V) (hW : ∀ g, W.map (ρ g).toLinearMap=W)
    [Group.IsSolvable (subspaceRepresentation ρ W hW).range]
    [Group.IsSolvable (quotientRepresentation ρ W hW).range] : Group.IsSolvable G := by
  let σ := subspaceRepresentation ρ W hW
  let τ := quotientRepresentation ρ W hW
  let ψ := σ.rangeRestrict.prod τ.rangeRestrict
  have hker : Group.IsSolvable ψ.ker := by
    apply Group.isSolvable_of_comm
    intro x y
    apply Subtype.ext
    apply hρ
    change ρ (x.val*y.val)=ρ (y.val*x.val)
    rw [map_mul,map_mul]
    have hs (g : ψ.ker) : σ g.val=1 := by
      have he := congrArg (fun z : σ.range × τ.range => (z.1 : W ≃ₗ[K] W)) g.property
      exact he
    have ht (g : ψ.ker) : τ g.val=1 := by
      have he := congrArg (fun z : σ.range × τ.range => (z.2 : (V ⧸ W) ≃ₗ[K] (V ⧸ W))) g.property
      exact he
    have hsub (g : ψ.ker) (w : V) (hw : w∈W) : ρ g.val w=w :=
      congrArg (fun e : W ≃ₗ[K] W => (e ⟨w,hw⟩ : V)) (hs g)
    have hquot (g : ψ.ker) (v : V) : ρ g.val v-v∈W := by
      apply (Submodule.Quotient.eq W).mp
      exact congrArg (fun e : (V ⧸ W) ≃ₗ[K] (V ⧸ W) => e (Submodule.Quotient.mk v)) (ht g)
    exact commute_of_identity_on_subspace_quotient W (ρ x.val) (ρ y.val)
      (hsub x) (hsub y) (hquot x) (hquot y)
  let := hker
  exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ (by simp)

end CriticalPercolation.LinearGrowth
end
end

end OAI
