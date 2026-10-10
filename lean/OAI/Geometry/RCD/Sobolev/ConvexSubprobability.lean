import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

namespace OAI

/-! # Finite subprobability combinations in a convex set containing zero -/

open Set
open scoped BigOperators
noncomputable section
namespace RegularPointCoordinates
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem convex_subprobability_sum_mem {K : Set E} (hK : Convex ℝ K) (h0 : 0 ∈ K)
    {m : ℕ} (v : Fin m → E) (hv : ∀ i, v i ∈ K) (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ 1) : (∑ i, w i • v i) ∈ K := by
  classical
  let w' : Fin (m+1) → ℝ := Fin.cons (1-∑ i, w i) w
  let v' : Fin (m+1) → E := Fin.cons 0 v
  have hw' : ∀ i ∈ (Finset.univ : Finset (Fin (m+1))), 0 ≤ w' i := by
    intro i _
    refine Fin.cases ?_ (fun j => ?_) i
    · exact sub_nonneg.mpr hsum
    · exact hw j
  have hsum' : ∑ i, w' i = 1 := by
    simp only [w',Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    ring
  have hv' : ∀ i ∈ (Finset.univ : Finset (Fin (m+1))), v' i ∈ K := by
    intro i _
    exact Fin.cases h0 hv i
  have hh := hK.sum_mem hw' hsum' hv'
  simpa only [w',v',Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,smul_zero,zero_add] using hh

end RegularPointCoordinates

end

end OAI
