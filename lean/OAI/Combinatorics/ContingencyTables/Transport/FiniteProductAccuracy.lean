import OAI.Combinatorics.ContingencyTables.Counting.AnnealingMultipliers
import OAI.Combinatorics.ContingencyTables.Counting.CompanionReferenceAccuracy

namespace OAI

/-! # Relative accuracy of the finite product used by the weight oracle -/

namespace ContingencyTables.FiniteProductAccuracy

open scoped BigOperators Classical

variable {J : Type*} [Fintype J]

lemma relative_log (x y delta : ℝ) (hy : 0 < y) (hd0 : 0 ≤ delta) (hd : delta ≤ 1/4)
    (herr : |x-y| ≤ delta*y) : 0 < x ∧ |Real.log (x/y)| ≤ 4*delta := by
  have hh := abs_le.mp herr
  have hx : (1-delta)*y ≤ x ∧ x ≤ (1+delta)*y := by constructor <;> nlinarith
  have h1 : (1-delta)*(1:ℝ) ≤ 1 ∧ (1:ℝ) ≤ (1+delta)*1 := by constructor <;> nlinarith
  have hp := AnnealingMultipliers.relative_ratio hy (by norm_num : (0:ℝ)<1) hd0 hd hx h1
  refine ⟨AnnealingMultipliers.empirical_positive hy hd hx.1,?_⟩
  simpa only [mul_one,one_mul] using hp.2.2.2

lemma product_log (x y : J → ℝ) (hy : ∀ j,0 < y j) (delta : ℝ)
    (hd0 : 0 ≤ delta) (hd : delta ≤ 1/4) (herr : ∀ j,|x j-y j| ≤ delta*y j) :
    0 < ∏ j,x j ∧ |Real.log ((∏ j,x j)/(∏ j,y j))| ≤ 4*(Fintype.card J:ℝ)*delta := by
  have hstep := fun j => relative_log (x j) (y j) delta (hy j) hd0 hd (herr j)
  refine ⟨Finset.prod_pos (fun j _ => (hstep j).1),?_⟩
  rw [←Finset.prod_div_distrib,Real.log_prod (fun j _ => div_ne_zero (hstep j).1.ne' (hy j).ne')]
  calc
    _ ≤ ∑ j,|Real.log (x j/y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : J,4*delta := Finset.sum_le_sum (fun j _ => (hstep j).2)
    _ = _ := by simp; ring

/-- The source has j+1 factors, each observed to the same tolerance.
This scalar budget is sufficient for its requested relative interval. -/
theorem product_relative (x y : J → ℝ) (hy : ∀ j,0 < y j) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (herr : ∀ j,|x j-y j| ≤ (epsilon/(200*(Fintype.card J:ℝ)))*y j)
    (hcard : 0 < Fintype.card J) :
    (1-epsilon/4)*(∏ j,y j) ≤ ∏ j,x j ∧
      (∏ j,x j) ≤ (1+epsilon/4)*(∏ j,y j) := by
  have hc : (0:ℝ) < Fintype.card J := by exact_mod_cast hcard
  have hc1 : (1:ℝ) ≤ Fintype.card J := by exact_mod_cast hcard
  have hd0 : 0 ≤ epsilon/(200*(Fintype.card J:ℝ)) := by positivity
  have hd : epsilon/(200*(Fintype.card J:ℝ)) ≤ 1/4 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ)<200*(Fintype.card J:ℝ))]
    linarith
  have hh := product_log x y hy _ hd0 hd herr
  have hb : 4*(Fintype.card J:ℝ)*(epsilon/(200*(Fintype.card J:ℝ)))=epsilon/50 := by
    field_simp [hc.ne']
    ring
  have ht := Finset.prod_pos (s := Finset.univ) (fun j _ => hy j)
  have hr := CompanionReferenceAccuracy.relative_of_log_error epsilon
    ((∏ j,x j)/(∏ j,y j)) he0 he1 (div_pos hh.1 ht) (hh.2.trans_eq hb)
  exact ⟨(le_div_iff₀ ht).mp hr.1,(div_le_iff₀ ht).mp hr.2⟩

end ContingencyTables.FiniteProductAccuracy

end OAI
