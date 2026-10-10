import Mathlib

namespace OAI

section
namespace PartialPermutation
namespace YoungTabloid
noncomputable section
open Finset
open scoped Classical

def row (μ : YoungDiagram) (x : μ.cells) : ℕ := x.1.1
def col (μ : YoungDiagram) (x : μ.cells) : ℕ := x.1.2

def Tabloid (μ : YoungDiagram) :=
  {r : μ.cells → ℕ // ∃ p : Equiv.Perm μ.cells, r = fun x => row μ (p x)}

def ofPerm (μ : YoungDiagram) (p : Equiv.Perm μ.cells) : Tabloid μ :=
  ⟨fun x => row μ (p x),p,rfl⟩

lemma ofPerm_surjective (μ : YoungDiagram) : Function.Surjective (ofPerm μ) := by
  rintro ⟨r,p,rfl⟩
  exact ⟨p,rfl⟩

instance (μ : YoungDiagram) : Finite (Tabloid μ) :=
  Finite.of_surjective (ofPerm μ) (ofPerm_surjective μ)
instance (μ : YoungDiagram) : Fintype (Tabloid μ) := Fintype.ofFinite _

def canonical (μ : YoungDiagram) : Tabloid μ := ofPerm μ 1

def relabel (μ : YoungDiagram) (g : Equiv.Perm μ.cells) (r : Tabloid μ) : Tabloid μ := by
  refine ⟨fun x => r.1 (g⁻¹ x),?_⟩
  obtain ⟨p,hp⟩ := r.2
  exact ⟨g⁻¹.trans p,by rw [hp]; rfl⟩

@[simp] lemma relabel_apply (μ : YoungDiagram) (g : Equiv.Perm μ.cells) (r : Tabloid μ)
    (x : μ.cells) : (relabel μ g r).1 x=r.1 (g⁻¹ x) := rfl

lemma relabel_one (μ : YoungDiagram) (r : Tabloid μ) : relabel μ 1 r=r := by rfl
lemma relabel_mul (μ : YoungDiagram) (g h : Equiv.Perm μ.cells) (r : Tabloid μ) :
    relabel μ (g*h) r=relabel μ g (relabel μ h r) := by
  apply Subtype.ext
  funext x
  simp only [relabel_apply,mul_inv_rev,Equiv.Perm.mul_apply]

def relabelEquiv (μ : YoungDiagram) (g : Equiv.Perm μ.cells) : Equiv.Perm (Tabloid μ) where
  toFun := relabel μ g
  invFun := relabel μ g⁻¹
  left_inv r := by rw [← relabel_mul,inv_mul_cancel,relabel_one]
  right_inv r := by rw [← relabel_mul,mul_inv_cancel,relabel_one]

lemma rowSum (μ : YoungDiagram) (r : Tabloid μ) :
    (∑ x, r.1 x) = ∑ x, row μ x := by
  obtain ⟨p,hp⟩ := r.2
  rw [hp]
  exact Fintype.sum_equiv p _ _ (fun _ => rfl)

def columnGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm μ.cells) where
  carrier := {g | ∀ x, col μ (g x)=col μ x}
  one_mem' _ := rfl
  mul_mem' hg hh x := (hg _).trans (hh x)
  inv_mem' := by
    intro g hg x
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hg (g⁻¹ x)).symm

def Col (μ : YoungDiagram) (j : ℕ) := {x : μ.cells // col μ x=j}

instance (μ : YoungDiagram) (j : ℕ) : Fintype (Col μ j) := by dsimp [Col]; infer_instance

def columnEquiv (μ : YoungDiagram) (j : ℕ) : Col μ j ≃ Fin (μ.colLen j) where
  toFun x := ⟨row μ x.1, by
    have h := μ.mem_iff_lt_colLen.mp x.1.2
    have hj : x.1.1.2=j := x.2
    simpa only [row, hj] using h⟩
  invFun i := ⟨⟨(i,j),μ.mem_iff_lt_colLen.mpr i.2⟩,rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl x.2.symm
  right_inv _ := rfl

lemma col_card (μ : YoungDiagram) (j : ℕ) : Fintype.card (Col μ j)=μ.colLen j := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (columnEquiv μ j)

end
end YoungTabloid
end PartialPermutation
end

end OAI
