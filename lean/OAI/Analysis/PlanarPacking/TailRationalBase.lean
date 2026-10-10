import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma min_div_lower {u D D₀ : ℝ} (hD₀ : 0 < D₀) (hD : D₀ ≤ D) :
    min u 0/D₀  ≤  u/D := by
  by_cases hu : 0 ≤ u
  · rw [min_eq_right hu,zero_div]
    exact div_nonneg hu (hD₀.le.trans hD)
  · rw [min_eq_left (le_of_not_ge hu)]
    apply (div_le_div_iff₀ hD₀ (hD₀.trans_le hD)).mpr
    exact mul_le_mul_of_nonpos_left hD (le_of_not_ge hu)
lemma rational_pair_lower {u v s s₀ n : ℝ}
    (hn : 0 ≤ n) (hn₀ : n < s₀) (hs : s₀ ≤ s) :
    min u 0/(s₀-n)^2+min v 0*n/(s₀*(s₀-n))  ≤ 
      u/(s-n)^2+v*n/(s*(s-n)) := by
  have hn₁ : 0 < s₀-n := sub_pos.mpr hn₀
  have hs₀ : 0 < s₀ := hn.trans_lt hn₀
  have hc' : min u 0/(s₀-n)^2  ≤  u/(s-n)^2 := by
    apply min_div_lower (sq_pos_of_pos hn₁)
    nlinarith
  have hd' : min v 0/(s₀*(s₀-n))  ≤  v/(s*(s-n)) := by
    apply min_div_lower (mul_pos hs₀ hn₁)
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (by linarith : 0 ≤ s-n)]
  have hd:=mul_le_mul_of_nonneg_right hd' hn
  convert add_le_add hc' hd using 1 <;> first | rfl | ring
lemma rational_finite_lower {ι : Type*} [Fintype ι]
    (c d n : ι → ℝ) (C s₀ s : ℝ)
    (hn : ∀ i,0 ≤ n i) (hn₀ : ∀ i,n i < s₀) (hs₀ : 0 < s₀) (hs : s₀ ≤ s) :
    C+min (∑ i,d i) 0/s₀+
      ∑ i,(min (c i) 0/(s₀-n i)^2+min (d i) 0*n i/(s₀*(s₀-n i)))  ≤ 
    C+∑ i,(c i/(s-n i)^2+d i/(s-n i)) := by
  have hd:=min_div_lower (u:=∑ i,d i) hs₀ hs
  have hp:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    rational_pair_lower (u:=c i) (v:=d i) (hn i) (hn₀ i) hs)
  have hsne : s≠0 := (hs₀.trans_le hs).ne'
  have he (i : ι) : d i/(s-n i)=d i/s+d i*n i/(s*(s-n i)) := by
    have hne : s-n i≠0 := (sub_pos.mpr ((hn₀ i).trans_le hs)).ne'
    field_simp; ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,← Finset.sum_div] at hp ⊢
  linarith
end SharpPlanar

end OAI
