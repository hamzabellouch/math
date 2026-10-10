import Mathlib
import OAI.RepresentationTheory.PartialPermutation.ColumnSorting

namespace OAI

section
namespace PartialPermutation
namespace YoungTabloid
noncomputable section
open Finset
open scoped Classical

def signC {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) : ℂ :=
  (Equiv.Perm.sign g : ℤ)

@[simp] lemma signC_one {α : Type*} [Fintype α] [DecidableEq α] : signC (1 : Equiv.Perm α)=1 := by
  simp [signC]
@[simp] lemma signC_mul {α : Type*} [Fintype α] [DecidableEq α] (g h : Equiv.Perm α) :
    signC (g*h)=signC g*signC h := by simp [signC]
@[simp] lemma signC_inv {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) :
    signC g⁻¹=signC g := by simp [signC]
@[simp] lemma signC_sq {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) :
    signC g*signC g=1 := by
  simpa using (signC_mul g g⁻¹).symm
@[simp] lemma signC_swap {α : Type*} [Fintype α] [DecidableEq α] (x y : α) (h : x≠y) :
    signC (Equiv.swap x y) = -1 := by simp [signC,Equiv.Perm.sign_swap h]

lemma swap_mem_column (μ : YoungDiagram) (x y : μ.cells) (h : col μ x=col μ y) :
    Equiv.swap x y ∈ columnGroup μ := by
  intro z
  by_cases hx : z=x
  · subst z; simpa using h.symm
  by_cases hy : z=y
  · subst z; simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

lemma relabel_swap_fix (μ : YoungDiagram) (r : Tabloid μ) (x y : μ.cells)
    (h : r.1 x=r.1 y) : relabel μ (Equiv.swap x y) r=r := by
  apply Subtype.ext
  funext z
  change r.1 ((Equiv.swap x y)⁻¹ z)=r.1 z
  rw [Equiv.swap_inv]
  by_cases hx : z=x
  · subst z; simpa using h.symm
  by_cases hy : z=y
  · subst z; simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

def Alternating (μ : YoungDiagram) (f : Tabloid μ → ℂ) : Prop :=
  ∀ (c : columnGroup μ) r, f (relabel μ c r)=signC c.1*f r

lemma alternating_zero_nontransversal (μ : YoungDiagram) (f : Tabloid μ → ℂ)
    (hf : Alternating μ f) (r : Tabloid μ) (hr : ¬Transversal μ r) : f r=0 := by
  simp only [Transversal,not_forall] at hr
  obtain ⟨x,y,h⟩ := hr
  obtain ⟨hc,he,hne⟩ := h
  have hz := hf ⟨Equiv.swap x y,swap_mem_column μ x y hc⟩ r
  change f (relabel μ (Equiv.swap x y) r)=signC (Equiv.swap x y)*f r at hz
  rw [relabel_swap_fix μ r x y he] at hz
  erw [signC_swap x y hne] at hz
  linear_combination hz / 2

lemma relabel_canonical (μ : YoungDiagram) (c : columnGroup μ) :
    (relabel μ c (canonical μ)).1 = fun x => row μ (c.1⁻¹ x) := rfl

lemma column_canonical_injective (μ : YoungDiagram) :
    Function.Injective (fun c : columnGroup μ => relabel μ c (canonical μ)) := by
  intro c d h
  have h' : c⁻¹=d⁻¹ := column_row_injective μ (congrArg Subtype.val h)
  exact inv_injective h'

lemma transversal_column_orbit (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) :
    ∃ c : columnGroup μ, r=relabel μ c (canonical μ) := by
  obtain ⟨c,hc⟩ := transversal_eq_column μ r hr
  refine ⟨c⁻¹,Subtype.ext ?_⟩
  change r.1 = fun x => row μ ((c.1⁻¹)⁻¹ x)
  simpa only [inv_inv] using hc

lemma alternating_eq_of_canonical_eq (μ : YoungDiagram) (f g : Tabloid μ → ℂ)
    (hf : Alternating μ f) (hg : Alternating μ g) (h : f (canonical μ)=g (canonical μ)) :
    f=g := by
  funext r
  by_cases hr : Transversal μ r
  · obtain ⟨c,rfl⟩ := transversal_column_orbit μ r hr
    rw [hf,hg,h]
  · rw [alternating_zero_nontransversal μ f hf r hr,
      alternating_zero_nontransversal μ g hg r hr]

end
end YoungTabloid
end PartialPermutation
end

end OAI
