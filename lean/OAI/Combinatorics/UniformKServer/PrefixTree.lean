import Mathlib
import OAI.Combinatorics.UniformKServer.RankedTree

namespace OAI

                                 
section

/-! The full fixed finite wordPrefix universe. Its vertices include every formal
wordPrefix, without deleting presently empty branches. -/
noncomputable section
namespace UniformKServer.PrefixTree
open TreeRounding TreeAncestry TreeLeaves
open scoped Classical

abbrev Word (A : Type*) (J : ℕ) := Σ d : Fin (J+1), Fin d.val → A
variable {A : Type*} [Fintype A] {J : ℕ}

def root : Word A J := ⟨0,Fin.elim0⟩
def parent (v : Word A J) : Word A J :=
  if h : v.1.val=0 then root else
    ⟨⟨v.1.val-1,by have := v.1.isLt; omega⟩,fun i => v.2 ⟨i.val,by have hi := i.isLt; change i.val < v.1.val-1 at hi; omega⟩⟩

def ranked (A : Type*) [Fintype A] (J : ℕ) : RankedTree.Data (Word A J) where
  root := root
  parent := parent
  level := fun v => v.1.val
  level_root := rfl
  level_zero := by
    rintro ⟨d,p⟩ hd
    have he : d=0 := Fin.ext hd
    subst d
    change (⟨0,p⟩ : Word A J)=⟨0,Fin.elim0⟩
    exact congrArg (fun f : Fin 0 → A => (⟨0,f⟩ : Word A J)) (funext fun i => Fin.elim0 i)
  step := by
    intro v hv
    have hn : v.1.val ≠ 0 := by
      intro hz
      apply hv
      rcases v with ⟨d,p⟩
      have he : d=0 := Fin.ext hz
      subst d
      change (⟨0,p⟩ : Word A J)=⟨0,Fin.elim0⟩
      exact congrArg (fun f : Fin 0 → A => (⟨0,f⟩ : Word A J)) (funext fun i => Fin.elim0 i)
    simp only [parent,dite_eq_right hn]
    omega

abbrev size (A : Type*) [Fintype A] (J : ℕ) := RankedTree.size (ranked A J)
def shape (A : Type*) [Fintype A] (J : ℕ) : Shape (size A J) := RankedTree.shape (ranked A J)
def chart (A : Type*) [Fintype A] (J : ℕ) : Vertex (size A J) ≃ Word A J := RankedTree.chart (ranked A J)

def wordPrefix (p : Fin J → A) (d : ℕ) (hd : d ≤ J) : Word A J :=
  ⟨⟨d,by omega⟩,fun i => p ⟨i.val,by omega⟩⟩
def atLevel (p : Fin J → A) (d : ℕ) (hd : d ≤ J) : Vertex (size A J) :=
  (chart A J).symm (wordPrefix p d hd)
def endpoint (p : Fin J → A) : Vertex (size A J) := atLevel p J le_rfl

theorem depth_chart (v : Vertex (size A J)) : depth (shape A J) v=(chart A J v).1.val :=
  RankedTree.depth_eq (ranked A J) v

theorem depth_at (p : Fin J → A) (d : ℕ) (hd : d ≤ J) : depth (shape A J) (atLevel p d hd)=d := by
  rw [depth_chart]
  simp only [atLevel,Equiv.apply_symm_apply,wordPrefix]

theorem depth_bound (v : Vertex (size A J)) : depth (shape A J) v ≤ J := by
  rw [depth_chart]
  exact Nat.le_of_lt_succ (chart A J v).1.isLt

theorem at_nonzero (p : Fin J → A) (d : ℕ) (hd : d ≤ J) (hpos : 0 < d) : atLevel p d hd ≠ 0 := by
  intro hz
  have he := depth_at p d hd
  rw [hz,depth_root] at he
  omega

omit [Fintype A] in
theorem prefix_parent (p : Fin J → A) (d : ℕ) (hd : d+1 ≤ J) :
    parent (wordPrefix p (d+1) hd)=wordPrefix p d (by omega) := by
  unfold parent
  rw [dite_eq_right (show (wordPrefix p (d+1) hd).1.val ≠ 0 by change d+1 ≠ 0; omega)]
  rfl

theorem at_parent (p : Fin J → A) (d : ℕ) (hd : d+1 ≤ J) :
    (shape A J).parent (atLevel p (d+1) hd)=atLevel p d (by omega) := by
  unfold shape
  rw [RankedTree.shape_parent (ranked A J) _ (at_nonzero p (d+1) hd (by omega))]
  simp only [atLevel,chart,Equiv.apply_symm_apply]
  exact congrArg (RankedTree.chart (ranked A J)).symm (prefix_parent p d hd)

theorem at_descends (p : Fin J → A) (d e : ℕ) (he : e ≤ J) (hde : d ≤ e) :
    descends (shape A J) (atLevel p d (hde.trans he)) (atLevel p e he) := by
  induction e,hde using Nat.le_induction with
  | base => exact desc_refl _
  | succ e hde ih =>
    exact desc_tail (ih (by omega)) (at_nonzero p (e+1) he (by omega)) (at_parent p e he)

theorem endpoint_leaf (p : Fin J → A) : leaf (S:=shape A J) (endpoint p) := by
  intro c
  have hdep := depth_child (S:=shape A J) c.val c.property.1
  rw [c.property.2] at hdep
  have he : depth (shape A J) (endpoint p)=J := depth_at p J le_rfl
  rw [he] at hdep
  have hb := depth_bound c.val
  omega

theorem ancestor_endpoint (p : Fin J → A) (d : ℕ) (hd : d ≤ J) :
    ancestor (shape A J) d (endpoint p)=atLevel p d hd :=
  ancestor_unique d (at_descends p d J le_rfl hd) (depth_at p d hd)

theorem desc_endpoint (p : Fin J → A) (v : Vertex (size A J))
    (h : descends (shape A J) v (endpoint p)) :
    v=atLevel p (depth (shape A J) v) (depth_bound v) := by
  have he := ancestor_unique (depth (shape A J) v) h rfl
  rw [ancestor_endpoint p _ (depth_bound v)] at he
  exact he.symm

end UniformKServer.PrefixTree

end


end

end OAI
