import Mathlib

namespace OAI

section
namespace SharpLogRamsey.TreePotential
open BinaryTree
variable {α : Type*}

def total (f : α → ℝ) : BinaryTree α → ℝ
  | .nil => 0
  | .node a l r => f a + total f l + total f r

def root (f : α → ℝ) : BinaryTree α → ℝ
  | .nil => 0
  | .node a _ _ => f a

def Admissible (f : α → ℝ) (K : ℝ) : BinaryTree α → Prop
  | .nil => True
  | .node a l r => 0≤f a ∧ root f l+root f r≤f a+K ∧
    Admissible f K l ∧ Admissible f K r

lemma root_nonneg (f : α → ℝ) (K : ℝ) {t : BinaryTree α} (h : Admissible f K t) :
    0≤root f t := by
  cases t with
  | nil => rfl
  | node a l r => exact h.1

lemma total_nonneg (f : α → ℝ) (K : ℝ) {t : BinaryTree α} (h : Admissible f K t) :
    0≤total f t := by
  induction t with
  | nil => rfl
  | node a l r hl hr => exact add_nonneg (add_nonneg h.1 (hl h.2.2.1)) (hr h.2.2.2)

theorem total_le_height (f : α → ℝ) (K : ℝ) (hK : 0≤K)
    (t : BinaryTree α) (h : Admissible f K t) :
    total f t≤(t.height:ℝ)*(root f t+(t.numNodes:ℝ)*K) := by
  induction t with
  | nil => simp [total,root]
  | node a l r hl hr =>
    rcases h with ⟨ha,hbranch,hleft,hright⟩
    have hln := root_nonneg f K hleft
    have hrn := root_nonneg f K hright
    have ihl := hl hleft
    have ihr := hr hright
    have hhl : (l.height:ℝ)≤(max l.height r.height:ℝ) := by exact_mod_cast le_max_left _ _
    have hhr : (r.height:ℝ)≤(max l.height r.height:ℝ) := by exact_mod_cast le_max_right _ _
    have hL := mul_le_mul_of_nonneg_right hhl (add_nonneg hln (by positivity : 0≤(l.numNodes:ℝ)*K))
    have hR := mul_le_mul_of_nonneg_right hhr (add_nonneg hrn (by positivity : 0≤(r.numNodes:ℝ)*K))
    have hB := mul_le_mul_of_nonneg_left hbranch (show 0≤(max l.height r.height:ℝ) by positivity)
    simp only [total,root,height,numNodes,Nat.cast_add,Nat.cast_one,Nat.cast_max]
    have hN : 0≤((l.numNodes:ℝ)+(r.numNodes:ℝ)+1)*K := by positivity
    nlinarith

lemma total_mono (f g : α → ℝ) (t : BinaryTree α) (h : ∀ a,f a≤g a) :
    total f t≤total g t := by
  induction t with
  | nil => rfl
  | node a l r hl hr => exact add_le_add (add_le_add (h a) hl) hr

lemma total_affine (f : α → ℝ) (c b : ℝ) (t : BinaryTree α) :
    total (fun a => c*(f a+b)) t=c*(total f t+(t.numNodes:ℝ)*b) := by
  induction t with
  | nil => simp [total]
  | node a l r hl hr => simp only [total,numNodes,Nat.cast_add,Nat.cast_one,hl,hr]; ring

theorem cost_bound (f cost : α → ℝ) (K c b : ℝ) (hK : 0≤K) (hc : 0≤c)
    (t : BinaryTree α) (h : Admissible f K t) (hcost : ∀ a,cost a≤c*(f a+b)) :
    total cost t≤c*((t.height:ℝ)*(root f t+(t.numNodes:ℝ)*K)+(t.numNodes:ℝ)*b) := by
  apply (total_mono cost (fun a => c*(f a+b)) t hcost).trans
  rw [total_affine]
  exact mul_le_mul_of_nonneg_left (add_le_add (total_le_height f K hK t h) le_rfl) hc

end SharpLogRamsey.TreePotential

end

end OAI
