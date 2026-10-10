import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridTrace

lemma kernel_lp {ι : Type*} (S : Finset ι) (F : ι → ℝ) (p q U L : ℝ)
    (hpq : p.HolderConjugate q) (hU : 0 ≤ U) (hL : 0 ≤ L)
    (hF : ∀ e ∈ S, 0 ≤ F e) (hFs : ∀ e ∈ S, F e ≤ U)
    (hFl : ∑ e ∈ S, F e ≤ L) :
    (∑ e ∈ S, (F e)^q)^(1/q) ≤ U^(1/p)*L^(1/q) := by
  have hq1 : 1 < q := hpq.symm.lt
  have hqn : 0 ≤ 1/q := le_of_lt (one_div_pos.mpr hpq.symm.pos)
  have hsum : (∑ e ∈ S, (F e)^q) ≤ U^(q-1)*L := by
    calc
      _ = ∑ e ∈ S, F e*(F e)^(q-1) := by
        apply Finset.sum_congr rfl
        intro e he
        calc
          _ = (F e)^(1+(q-1)) := by congr 1;ring
          _ = (F e)^1*(F e)^(q-1) := Real.rpow_add' (hF e he) (by linarith)
          _ = _ := by rw [Real.rpow_one]
      _ ≤ ∑ e ∈ S, F e*U^(q-1) := by
        apply Finset.sum_le_sum
        intro e he
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hF e he) (hFs e he) (by linarith)) (hF e he)
      _ = U^(q-1)*∑ e ∈ S, F e := by rw [← Finset.sum_mul,mul_comm]
      _ ≤ U^(q-1)*L := mul_le_mul_of_nonneg_left hFl (Real.rpow_nonneg hU _)
  have hr := Real.rpow_le_rpow (Finset.sum_nonneg (fun e he => Real.rpow_nonneg (hF e he) _)) hsum hqn
  calc
    _ ≤ _ := hr
    _ = U^(1/p)*L^(1/q) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hU _) hL,← Real.rpow_mul hU]
      congr 2
      have heq := hpq.inv_add_inv_eq_one
      rw [one_div,one_div]
      field_simp [hpq.ne_zero,hpq.symm.ne_zero] at heq ⊢
      linarith

lemma kernel_holder {ι : Type*} (S : Finset ι) (F g : ι → ℝ) (p q U L : ℝ)
    (hpq : p.HolderConjugate q) (hU : 0 ≤ U) (hL : 0 ≤ L)
    (hF : ∀ e ∈ S, 0 ≤ F e) (hFs : ∀ e ∈ S, F e ≤ U)
    (hFl : ∑ e ∈ S, F e ≤ L) (hg : ∀ e ∈ S, 0 ≤ g e) :
    (∑ e ∈ S, F e*g e) ≤ U^(1/p)*L^(1/q)*(∑ e ∈ S, (g e)^p)^(1/p) := by
  refine (Real.inner_le_Lp_mul_Lq_of_nonneg S hpq.symm hF hg).trans ?_
  exact mul_le_mul_of_nonneg_right (kernel_lp S F p q U L hpq hU hL hF hFs hFl)
    (Real.rpow_nonneg (Finset.sum_nonneg (fun e he => Real.rpow_nonneg (hg e he) _)) _)

lemma dyadic_sum_bound (β : ℝ) (hβ : 0 < β) (M : ℕ) :
    (∑ k ∈ Finset.range M, ((2:ℝ)^k)^β) ≤ ((2:ℝ)^M)^β/((2:ℝ)^β-1) := by
  have hbase : 1 < (2:ℝ)^β := Real.one_lt_rpow (by norm_num) hβ
  have hid (k : ℕ) : ((2:ℝ)^k)^β = ((2:ℝ)^β)^k := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num),← Real.rpow_mul_natCast (by norm_num)]
    congr 1;ring
  simp_rw [hid]
  rw [geom_sum_eq (ne_of_gt hbase)]
  exact div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (sub_nonneg.mpr hbase.le)

end GridTrace

end

end OAI
