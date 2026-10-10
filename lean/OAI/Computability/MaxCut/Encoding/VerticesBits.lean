import Mathlib
import OAI.Computability.MaxCut.Analysis.CubeEquiv
import OAI.Computability.MaxCut.Estimates.ListSum

namespace OAI

noncomputable section
namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset MaxCutGames.Foundations.Target MaxCutGames.Foundations.Hastad
open LongCode LongCode.InstanceAdapter CounterMachine.Expr
attribute [local instance] Classical.propDecidable

@[simp] theorem vertices_bits {q : ℕ} (g : Instance q) : vertices (bits g) = g.vertices := (word_header g).1
@[simp] theorem edges_bits {q : ℕ} (g : Instance q) : edges (bits g) = g.constraints.length := (word_header g).2.2
@[simp] theorem row_source {q : ℕ} (g : Instance q) (e : Fin g.constraints.length) :
    row q (bits g) e 0 = g.constraints[e].source.val := by
  simpa [row] using InstanceAdapter.row_source g e
@[simp] theorem row_target {q : ℕ} (g : Instance q) (e : Fin g.constraints.length) :
    row q (bits g) e 1 = g.constraints[e].target.val := InstanceAdapter.row_target g e
@[simp] theorem row_image {q : ℕ} (g : Instance q) (e : Fin g.constraints.length) (i : Fin q) :
    row q (bits g) e (2+i.val) = g.constraints[e].permutation.images[i].val := InstanceAdapter.row_image g e i

@[simp] theorem degree_bits {q : ℕ} (g : Instance q) (y : Fin g.vertices) :
    degree q (bits g) y = InstanceAdapter.degree g y := by
  rw [degree, edges_bits, ← Fin.sum_univ_eq_sum_range]
  unfold InstanceAdapter.degree
  apply sum_congr rfl
  intro e he
  rw [row_target]
  simp only [Fin.val_inj]

@[simp] theorem lookup_fin {q : ℕ} (x : Cube (Fin q)) (i : Fin q) :
    lookup x i.val = (finTwoEquiv.symm (x i)).val := by
  simp [lookup, Fin.val_inj]

@[simp] theorem permCode_bits {q : ℕ} (g : Instance q) (e : Fin g.constraints.length)
    (x : Cube (Fin q)) :
    permCode (bits g) e x = (cubeEquiv q (cubePerm (MaxCutGames.Explicit.MachineOutputContract.permutationEquiv g.constraints[e].permutation) x)).val := by
  simp only [permCode, row_image, lookup_fin, cubeEquiv, Equiv.trans_apply, finFunctionFinEquiv_apply]
  rfl

@[simp] theorem query_bits {q : ℕ} (g : Instance q) (e : Fin g.constraints.length)
    (x : Cube (Fin q)) :
    query (bits g) e x = (vertexEquiv g.vertices q
      (g.constraints[e].source,cubePerm (MaxCutGames.Explicit.MachineOutputContract.permutationEquiv g.constraints[e].permutation) x)).val := by
  simp only [query, permCode_bits, row_source]
  rfl

@[simp] theorem gridSize_bits {q : ℕ} (g : Instance q) (K : ℕ) :
    gridSize q K (bits g) = Game.gridSize (Fin g.vertices) (Fin g.constraints.length) q K := by
  simp [gridSize, Game.gridSize, Game.Sample, vertices_bits, edges_bits]

 theorem rational_floor (c : ℚ) (hc : 0 ≤ c) (P d m : ℕ) :
    ⌊(P:ℚ)*((d:ℚ)*c/((m:ℚ)*(d:ℚ)^2))⌋₊ =
      P*d*c.num.toNat/(c.den*m*d^2) := by
  have hn : ((c.num.toNat:ℕ):ℚ) = (c.num:ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hc)
  have hc' : c = ((c.num.toNat:ℕ):ℚ)/c.den := by rw [hn, Rat.num_div_den]
  conv_lhs => rw [hc']
  have he : (P:ℚ)*((d:ℚ)*(((c.num.toNat:ℕ):ℚ)/c.den)/((m:ℚ)*(d:ℚ)^2)) =
      ((P*d*c.num.toNat:ℕ):ℚ)/((c.den*m*d^2:ℕ):ℚ) := by
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, Nat.floor_div_natCast, Nat.floor_natCast]

@[simp] theorem atom_bits {q : ℕ} (g : Instance q) (t : ℚ)
    (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) (y : Fin g.vertices)
    (e f : Fin g.constraints.length) (x z : Cube (Fin q)) :
    atom t ht K (bits g) y e f x z =
      ⌊(Game.gridSize (Fin g.vertices) (Fin g.constraints.length) q K:ℚ)*
        ((ofInstance g).sampleLaw t ht).weight (y,e,f,x,z)⌋₊ := by
  rw [InstanceAdapter.sampleLaw_weight]
  simp only [atom, row_target, Fin.val_inj, gridSize_bits, degree_bits, edges_bits]
  split_ifs
  · exact (rational_floor _ ((jointLaw t ht q).nonneg _) _ _ _).symm
  · simp

/-- Byte-oriented integer aggregation is exactly the rational rounded law.
This identity is independent of computational complexity assumptions. -/
theorem weights_bits {q : ℕ} (g : Instance q) (t : ℚ)
    (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (anchor : Fin (g.vertices*2^q)) (u v : Fin (g.vertices*2^q)) :
    (ofInstance g).gridWeights t ht (vertexEquiv g.vertices q) anchor K u v =
      (weights q t ht K (bits g) u.val v.val : ℚ) / gridSize q K (bits g) := by
  rw [Game.gridWeights, roundedWeights_integer, gridSize_bits]
  by_cases huv : u=v
  · subst v; simp [weights]
  · have hval : u.val ≠ v.val := fun h => huv (Fin.ext h)
    simp only [huv, ↓reduceIte, weights, hval, vertices_bits, edges_bits]
    congr 2
    rw [Fintype.sum_prod_type]
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro y hy
    rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro e he
    rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro f hf
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro x hx
    apply sum_congr rfl
    intro z hz
    simp only [query_bits, atom_bits, Game.queries, ofInstance, Prod.mk.injEq, ← Fin.val_inj]

end OptimalMaxCut.RawGrid

end

end OAI
