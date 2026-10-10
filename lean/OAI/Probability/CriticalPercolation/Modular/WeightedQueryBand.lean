import Mathlib
import OAI.Probability.CriticalPercolation.Modular.WeightedCauchy
import OAI.Probability.CriticalPercolation.Modular.WeightedQuery

namespace OAI

section
noncomputable section
open scoped Classical

namespace CriticalPercolation.FiniteEntropy
variable {X : Type*} [Fintype X]

lemma weighted_fourth_cauchy (W f h : X → ℝ) (hW : ∀ x, 0≤W x)
    (hh0 : ∀ x, 0≤h x) (hh1 : ∀ x, h x≤1) :
    (∑ x, W x*(h x*|f x|))^4 ≤ (∑ x, W x*(f x)^4)*(∑ x, W x*h x)^3 := by
  let L := ∑ x, W x*(h x*|f x|)
  let S := ∑ x, W x*(h x*(f x)^2)
  let P := ∑ x, W x*h x
  let Q := ∑ x, W x*(f x)^4
  have hP : 0≤P := Finset.sum_nonneg (fun x _ => mul_nonneg (hW x) (hh0 x))
  have hS : 0≤S := Finset.sum_nonneg (fun x _ => mul_nonneg (hW x) (mul_nonneg (hh0 x) (sq_nonneg _)))
  have h0 := weighted_cauchy (fun x => W x*h x) (fun x => |f x|) (fun _ => 1)
    (fun x => mul_nonneg (hW x) (hh0 x))
  have hL : L^2≤S*P := by simpa only [L,S,P,mul_one,one_pow,sq_abs,mul_assoc] using h0
  have h1 := weighted_cauchy (fun x => W x*h x) (fun x => (f x)^2) (fun _ => 1)
    (fun x => mul_nonneg (hW x) (hh0 x))
  have h2 : S^2≤(∑ x, W x*(h x*(f x)^4))*P := by
    simpa only [S,P,mul_one,one_pow,mul_assoc,←pow_mul] using h1
  have hQ : (∑ x, W x*(h x*(f x)^4))≤Q := by
    apply Finset.sum_le_sum
    intro x hx
    apply mul_le_mul_of_nonneg_left _ (hW x)
    exact mul_le_of_le_one_left (by positivity) (hh1 x)
  have hSQ : S^2≤Q*P := h2.trans (mul_le_mul_of_nonneg_right hQ hP)
  change L^4≤Q*P^3
  have hLs : L^4≤S^2*P^2 := by
    have hs := mul_nonneg (sub_nonneg.mpr hL) (add_nonneg (mul_nonneg hS hP) (sq_nonneg L))
    nlinarith
  have hSQ' := mul_le_mul_of_nonneg_right hSQ (sq_nonneg P)
  nlinarith

end CriticalPercolation.FiniteEntropy
namespace CriticalPercolation.SearchTree
open FiniteProduct

variable {E R : Type*} [Fintype E] [DecidableEq E]

theorem weighted_event_fourth (a : E → ℝ) (t : SearchTree E R)
    (used : Finset E) (ht : t.Valid used) (p : ℝ) (hp : p∈Set.Icc 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (B : ℝ) (hB : 0≤B)
    (h : (E → Prop) → ℝ) (hh0 : ∀ ω, 0≤h ω) (hh1 : ∀ ω, h ω≤1)
    (hcost : ∀ ω, h ω≠0 → t.quadraticCost a ω≤B) :
    (expect w (fun ω => h ω*|t.weightedSum a p ω|))^4 ≤
      5*B^2*(expect w h)^3 := by
  classical
  have heq : (fun ω => h ω*|t.weightedSum a p ω|) =
      (fun ω => h ω*|(t.takeQuadratic a B).weightedSum a p ω|) := by
    funext ω
    by_cases hh : h ω=0
    · simp only [hh,zero_mul]
    · rw [t.takeQuadratic_sum_eq a p B ω (hcost ω hh)]
  rw [heq]
  have hHolder := FiniteEntropy.weighted_fourth_cauchy (density w)
    (fun ω => (t.takeQuadratic a B).weightedSum a p ω) h (density_nonneg hn) hh0 hh1
  have hHolder' : (expect w (fun ω => h ω*|(t.takeQuadratic a B).weightedSum a p ω|))^4 ≤
    (expect w (fun ω => ((t.takeQuadratic a B).weightedSum a p ω)^4))*(expect w h)^3 := by
    convert hHolder using 1 <;> simp only [expect] <;> congr <;> exact Subsingleton.elim _ _
  exact hHolder'.trans (mul_le_mul_of_nonneg_right
    (expected_takeQuadratic_fourth a t used ht p hp w hw hn hf B hB)
    (pow_nonneg (expect_nonneg hn hh0) _))

end CriticalPercolation.SearchTree
end
end

end OAI
