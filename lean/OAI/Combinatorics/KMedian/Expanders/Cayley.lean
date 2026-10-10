import Mathlib
import OAI.Combinatorics.KMedian.Expanders.Walsh

namespace OAI

section Inline_PCPCayley

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Walsh
variable {I D : Type} [Fintype I] [DecidableEq I]

def cayleyRotate (g : D → BitVector I) (p : BitVector I × D) : BitVector I × D :=
  (p.1+g p.2,p.2)
omit [Fintype I] [DecidableEq I] in
lemma cayleyRotate_involutive (g : D → BitVector I) : Function.Involutive (cayleyRotate g) := by
  rintro ⟨v,d⟩
  unfold cayleyRotate
  congr 1
  have hg : g d+g d=0 := funext (fun i => CharTwo.add_self_eq_zero (g d i))
  rw [add_assoc,hg,add_zero]

def cayley (g : D → BitVector I) : PortGraph (BitVector I) D where
  rotate := { toFun := cayleyRotate g
              invFun := cayleyRotate g
              left_inv := cayleyRotate_involutive g
              right_inv := cayleyRotate_involutive g }
  involutive := cayleyRotate_involutive g

omit [Fintype I] [DecidableEq I] in
@[simp] lemma cayley_step (g : D → BitVector I) (v : BitVector I) (d : D) :
    (cayley g).step v d=v+g d := rfl

variable [Fintype D] [Nonempty D]
noncomputable def bias (g : D → BitVector I) (b : BitVector I) : ℝ := 𝔼 d, character b (g d)

omit [DecidableEq I] [Nonempty D] in
lemma adjacency_character (g : D → BitVector I) (b : BitVector I) :
    (cayley g).adjacency (character b) = fun v => character b v * bias g b := by
  funext v
  unfold PortGraph.adjacency
  simp_rw [cayley_step,character_add]
  rw [← mul_expect]
  rfl

omit [Nonempty D] in
lemma coefficient_adjacency (g : D → BitVector I) (f : BitVector I → ℝ) (b : BitVector I) :
    coefficient ((cayley g).adjacency f) b=coefficient f b*bias g b := by
  unfold coefficient
  rw [← PortGraph.adjacency_selfAdjoint,adjacency_character]
  unfold pairing
  simp_rw [← mul_assoc]
  rw [← expect_mul]

omit [Nonempty D] in
theorem cayley_contracts (g : D → BitVector I) (ρ : ℝ)
    (hbias : ∀ b, b≠0 → |bias g b| ≤ ρ) : (cayley g).Contracts ρ := by
  intro f hf
  rw [parseval,parseval,mul_sum]
  apply sum_le_sum
  intro b _
  rw [coefficient_adjacency]
  by_cases hb : b=0
  · subst b
    rw [coefficient_zero,hf]
    simp
  · have h := hbias b hb
    have hr : 0 ≤ ρ := (abs_nonneg _).trans h
    have hs : bias g b ^ 2 ≤ ρ^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (bias g b)) h 2
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (coefficient f b))]

end Walsh
end MetricKMedian.PCP

end Inline_PCPCayley

end OAI
