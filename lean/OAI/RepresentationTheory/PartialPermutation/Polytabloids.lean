import Mathlib
import OAI.RepresentationTheory.PartialPermutation.AlternatingTabloids

namespace OAI

section
namespace PartialPermutation
namespace YoungTabloid
noncomputable section
open Finset
open scoped Classical

def tabloidRep (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm μ.cells) (EuclideanSpace ℂ (Tabloid μ)) where
  toFun g :=
    { toFun := fun f => WithLp.toLp 2 (fun r => f (relabel μ g⁻¹ r))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f r; simp [relabel_one]
  map_mul' := by
    intro g h
    ext f r
    change f (relabel μ (g*h)⁻¹ r)=f (relabel μ h⁻¹ (relabel μ g⁻¹ r))
    rw [mul_inv_rev,relabel_mul]

@[simp] lemma tabloidRep_apply (μ : YoungDiagram) (g : Equiv.Perm μ.cells)
    (f : EuclideanSpace ℂ (Tabloid μ)) (r : Tabloid μ) :
    tabloidRep μ g f r=f (relabel μ g⁻¹ r) := rfl

lemma tabloidRep_unitary (μ : YoungDiagram) (g : Equiv.Perm μ.cells)
    (f h : EuclideanSpace ℂ (Tabloid μ)) :
    inner ℂ (tabloidRep μ g f) (tabloidRep μ g h)=inner ℂ f h := by
  simp only [PiLp.inner_apply,tabloidRep_apply]
  exact Fintype.sum_equiv (relabelEquiv μ g⁻¹) _ _ (fun _ => rfl)

def antisym (μ : YoungDiagram) : Module.End ℂ (EuclideanSpace ℂ (Tabloid μ)) :=
  ∑ c : columnGroup μ, signC c.1 • tabloidRep μ c.1

lemma antisym_apply (μ : YoungDiagram) (f : EuclideanSpace ℂ (Tabloid μ)) (r : Tabloid μ) :
    antisym μ f r = ∑ c : columnGroup μ, signC c.1 * f (relabel μ c.1⁻¹ r) := by
  simp [antisym,LinearMap.sum_apply,LinearMap.smul_apply]

lemma antisym_alternating (μ : YoungDiagram) (f : EuclideanSpace ℂ (Tabloid μ)) :
    Alternating μ (antisym μ f) := by
  intro d r
  rw [antisym_apply,antisym_apply,Finset.mul_sum]
  calc
    _ = ∑ c : columnGroup μ, signC (d*c).1 *
        f (relabel μ (d*c).1⁻¹ (relabel μ d.1 r)) :=
      (Fintype.sum_equiv (Equiv.mulLeft d) _ _ (fun _ => rfl)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      simp only [Subgroup.coe_mul,signC_mul,mul_inv_rev,← relabel_mul]
      simp only [mul_assoc,inv_mul_cancel,mul_one]

def delta (μ : YoungDiagram) (r : Tabloid μ) : EuclideanSpace ℂ (Tabloid μ) :=
  WithLp.toLp 2 (fun s => if s=r then 1 else 0)

def polytabloid (μ : YoungDiagram) : EuclideanSpace ℂ (Tabloid μ) :=
  antisym μ (delta μ (canonical μ))

lemma canonical_fix_iff (μ : YoungDiagram) (c : columnGroup μ) :
    relabel μ c (canonical μ)=canonical μ ↔ c=1 := by
  constructor
  · intro h
    exact column_canonical_injective μ (h.trans (relabel_one μ _).symm)
  · rintro rfl
    rfl

lemma polytabloid_canonical (μ : YoungDiagram) : polytabloid μ (canonical μ)=1 := by
  rw [polytabloid,antisym_apply]
  change (∑ c : columnGroup μ, signC c.1 *
    (if relabel μ c.1⁻¹ (canonical μ)=canonical μ then 1 else 0))=1
  have hh (c : columnGroup μ) : relabel μ c.1⁻¹ (canonical μ)=canonical μ ↔ c=1 := by
    change relabel μ (c⁻¹:columnGroup μ) (canonical μ)=canonical μ ↔ c=1
    rw [canonical_fix_iff,inv_eq_one]
  simp [hh]

lemma polytabloid_ne_zero (μ : YoungDiagram) : polytabloid μ≠0 := by
  intro h
  have hc := polytabloid_canonical μ
  rw [h] at hc
  exact zero_ne_one hc

lemma polytabloid_alternating (μ : YoungDiagram) : Alternating μ (polytabloid μ) :=
  antisym_alternating μ _

lemma antisym_rank_one (μ : YoungDiagram) (f : EuclideanSpace ℂ (Tabloid μ)) :
    antisym μ f = (antisym μ f (canonical μ)) • polytabloid μ := by
  apply PiLp.ext
  intro r
  have ha : Alternating μ (fun s => antisym μ f (canonical μ)*polytabloid μ s) := by
    intro c s
    dsimp only
    rw [polytabloid_alternating μ c s]
    ring
  exact congrFun (alternating_eq_of_canonical_eq μ _ _ (antisym_alternating μ f) ha
    (by rw [polytabloid_canonical,mul_one])) r

@[simp] lemma signC_conj {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) :
    starRingEnd ℂ (signC g)=signC g := by simp [signC]

lemma antisym_selfadjoint (μ : YoungDiagram) (f h : EuclideanSpace ℂ (Tabloid μ)) :
    inner ℂ (antisym μ f) h=inner ℂ f (antisym μ h) := by
  have hu (c : columnGroup μ) :
      inner ℂ (tabloidRep μ c.1 f) h=inner ℂ f (tabloidRep μ c.1⁻¹ h) := by
    have hh := tabloidRep_unitary μ c.1 f (tabloidRep μ c.1⁻¹ h)
    simpa using hh
  simp only [antisym,LinearMap.sum_apply,LinearMap.smul_apply,inner_sum,sum_inner,
    inner_smul_left,inner_smul_right,signC_conj,hu]
  exact Fintype.sum_equiv (Equiv.inv (columnGroup μ)) _ _ (fun c => by
    simp only [Equiv.inv_apply,Subgroup.coe_inv,signC_inv])

lemma inner_delta (μ : YoungDiagram) (r : Tabloid μ) (f : EuclideanSpace ℂ (Tabloid μ)) :
    inner ℂ (delta μ r) f=f r := by simp [PiLp.inner_apply,delta]

lemma antisym_eq_inner (μ : YoungDiagram) (f : EuclideanSpace ℂ (Tabloid μ)) :
    antisym μ f=inner ℂ (polytabloid μ) f • polytabloid μ := by
  rw [antisym_rank_one]
  congr 1
  rw [polytabloid,antisym_selfadjoint,inner_delta]

end
end YoungTabloid
end PartialPermutation
end

end OAI
