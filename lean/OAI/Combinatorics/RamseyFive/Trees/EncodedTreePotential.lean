import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.PivotTree

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) (M : ∀a c,Ω a c→Type z)
  (left right : ∀a c t,M a c t→C)
  (enc : ∀a c t,Option (M a c t))

omit [Fintype C] in
theorem encoded_potential_le (φ : C→ℝ) (B : ℝ) (hφ : ∀c,0≤φ c) (hB : 0≤B)
    (hsplit : ∀a c t m,enc a c t=some m→φ (left a c t m)+φ (right a c t m)≤φ c+B)
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) :
    cost Ω M left right (fun _ c _ _=>φ c) b ω c (encoded Ω M left right enc b ω c)≤
      b.height*(φ c+B*b.numNodes) := by
  induction b generalizing c with
  | nil => simp [cost]
  | node a l r ihl ihr =>
    cases he : enc a c (ω.1 c) with
    | none =>
      simp only [encoded,he,Option.map_none,cost]
      exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hφ c) (mul_nonneg hB (Nat.cast_nonneg _)))
    | some m =>
      have hl := ihl ω.2.1 (left a c (ω.1 c) m)
      have hr := ihr ω.2.2 (right a c (ω.1 c) m)
      have hL : (l.height:ℝ)≤ max l.height r.height := by exact_mod_cast le_max_left l.height r.height
      have hR : (r.height:ℝ)≤ max l.height r.height := by exact_mod_cast le_max_right l.height r.height
      have hl' := hl.trans (mul_le_mul_of_nonneg_right hL
        (add_nonneg (hφ _) (mul_nonneg hB (Nat.cast_nonneg l.numNodes))))
      have hr' := hr.trans (mul_le_mul_of_nonneg_right hR
        (add_nonneg (hφ _) (mul_nonneg hB (Nat.cast_nonneg r.numNodes))))
      have hs := mul_le_mul_of_nonneg_left (hsplit a c (ω.1 c) m he) (Nat.cast_nonneg (max l.height r.height))
      simp only [encoded,he,Option.map_some,cost,BinaryTree.height,BinaryTree.numNodes,
        Nat.cast_add,Nat.cast_one]
      nlinarith only [hl',hr',hs,mul_nonneg hB (Nat.cast_nonneg l.numNodes),
        mul_nonneg hB (Nat.cast_nonneg r.numNodes),hB]

omit [Fintype C] in
theorem encoded_cost_linear (φ : C→ℝ) (lc : ∀a c t,M a c t→ℝ)
    (X D : ℝ) (hD : 0≤D)
    (hlc : ∀a c t m,enc a c t=some m→lc a c t m≤X*φ c+D)
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) :
    cost Ω M left right lc b ω c (encoded Ω M left right enc b ω c)≤
      X*cost Ω M left right (fun _ c _ _=>φ c) b ω c (encoded Ω M left right enc b ω c)+D*b.numNodes := by
  induction b generalizing c with
  | nil => simp [cost]
  | node a l r ihl ihr =>
    cases he : enc a c (ω.1 c) with
    | none => simp only [encoded,he,Option.map_none,cost,mul_zero,zero_add];positivity
    | some m =>
      have hl := ihl ω.2.1 (left a c (ω.1 c) m)
      have hr := ihr ω.2.2 (right a c (ω.1 c) m)
      have hs := hlc a c (ω.1 c) m he
      simp only [encoded,he,Option.map_some,cost,BinaryTree.numNodes,Nat.cast_add,Nat.cast_one]
      linarith only [hl,hr,hs]

omit [Fintype C] in
theorem encoded_cost_le (φ : C→ℝ) (lc : ∀a c t,M a c t→ℝ)
    (B X D : ℝ) (hφ : ∀c,0≤φ c) (hB : 0≤B) (hX : 0≤X) (hD : 0≤D)
    (hsplit : ∀a c t m,enc a c t=some m→φ (left a c t m)+φ (right a c t m)≤φ c+B)
    (hlc : ∀a c t m,enc a c t=some m→lc a c t m≤X*φ c+D)
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) :
    cost Ω M left right lc b ω c (encoded Ω M left right enc b ω c)≤
      X*b.height*(φ c+B*b.numNodes)+D*b.numNodes := by
  have hc := encoded_cost_linear Ω M left right enc φ lc X D hD hlc b ω c
  have hp := mul_le_mul_of_nonneg_left
    (encoded_potential_le Ω M left right enc φ B hφ hB hsplit b ω c) hX
  nlinarith only [hc,hp]
end SharpRamseyFive.TreeCodec

end OAI
