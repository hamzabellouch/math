import OAI.NumberTheory.TwoPoint.Bounds.PrimeRowMoments

namespace OAI

/-! The rare-site row majorant has a fixed polynomial second moment,
uniformly in the band-width parameter W. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma prime_row_moment_product_bound {J : ℕ} (Q : Finset ℕ) (V : Fin J → ℝ)
    (L W : ℝ) (hL : 1 ≤ L) (hW : 10 ≤ W)
    (hQ : (∑ p ∈ Q, 1 / (p : ℝ)) ≤ Real.log L)
    (hV0 : ∀ j, 0 ≤ V j) (hV : ∀ j, V j ≤ 2 * W)
    (hJ : (J : ℝ) * (6 * W) ≤ Real.log L) :
    (∏ q : Q, (1 + 24 / (q.val : ℝ))) *
      (∏ j : Fin J, (4 * (V j) ^ 2 + V j)) ≤ L ^ (25 : ℕ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hQprod : (∏ q : Q, (1 + 24 / (q.val : ℝ))) ≤ Real.exp (24 * Real.log L) := by
    calc
      _ ≤ ∏ q : Q, Real.exp (24 / (q.val : ℝ)) := by
        apply prod_le_prod₀
        · intro q _
          positivity
        · intro q _
          simpa only [add_comm] using Real.add_one_le_exp (24 / (q.val : ℝ))
      _ = Real.exp (24 * ∑ p ∈ Q, 1 / (p : ℝ)) := by
        rw [← Real.exp_sum, ← sum_coe_sort Q (fun p : ℕ => 1 / (p : ℝ)), mul_sum]
        congr 1
        apply sum_congr rfl
        intro q _
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hbase : 18 * W ^ 2 ≤ Real.exp (6 * W) := by
    have hE : W ≤ Real.exp W := by linarith [Real.add_one_le_exp W]
    have hE4 : (18 : ℝ) ≤ Real.exp (4 * W) := by
      linarith [Real.add_one_le_exp (4 * W)]
    calc
      _ ≤ Real.exp (4 * W) * (Real.exp W) ^ 2 :=
        mul_le_mul hE4 (pow_le_pow_left₀ (by linarith) hE 2)
          (sq_nonneg W) (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
  have hVprod : (∏ j : Fin J, (4 * (V j) ^ 2 + V j)) ≤ Real.exp (Real.log L) := by
    calc
      _ ≤ ∏ _j : Fin J, Real.exp (6 * W) := by
        apply prod_le_prod₀
        · intro j _
          exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hV0 j)
        · intro j _
          have hv : 4 * (V j) ^ 2 + V j ≤ 18 * W ^ 2 := by
            have hs := mul_nonneg (hV0 j) (sub_nonneg.mpr (hV j))
            have ht := sq_nonneg (2 * W - V j)
            nlinarith [hV j, hV0 j]
          exact hv.trans hbase
      _ = Real.exp ((J : ℝ) * (6 * W)) := by
        simp only [prod_const, card_univ, Fintype.card_fin]
        rw [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr hJ
  calc
    _ ≤ Real.exp (24 * Real.log L) * Real.exp (Real.log L) :=
      mul_le_mul hQprod hVprod (prod_nonneg (fun j _ =>
        add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hV0 j))) (Real.exp_pos _).le
    _ = L ^ (25 : ℕ) := by
      rw [← Real.exp_add]
      rw [show 24 * Real.log L + Real.log L = (25 : ℕ) * Real.log L by norm_num; ring]
      rw [Real.exp_nat_mul, Real.exp_log hLp]

namespace FiniteLaw

lemma square_event_average_le {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (f : α → ℝ) (E : α → Prop) :
    (μ.average (fun x => f x * if E x then 1 else 0)) ^ 2 ≤
      μ.average (fun x => (f x) ^ 2) * μ.probability E := by
  have hh := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (f := fun x => μ.weight x * (f x) ^ 2)
    (g := fun x => μ.weight x * if E x then 1 else 0)
    (r := fun x => μ.weight x * (f x * if E x then 1 else 0))
    (fun x _ => mul_nonneg (μ.nonneg x) (sq_nonneg _))
    (fun x _ => mul_nonneg (μ.nonneg x) (by split_ifs <;> norm_num))
    (fun x _ => by split_ifs <;> ring_nf <;> exact le_rfl)
  exact hh

end FiniteLaw

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

theorem prime_row_second_moment_polynomial (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (P : Fin J → Finset ℕ) (hsub : ∀ j, P j ⊆ data.P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (site : ℤ)
    (L W : ℝ) (hL : 1 ≤ L) (hW : 10 ≤ W)
    (hQ : (∑ p ∈ data.Q, 1 / (p : ℝ)) ≤ Real.log L)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hJ : (J : ℝ) * (6 * W) ≤ Real.log L) :
    (data.residueLaw B hB).average (fun x =>
      (primeRowMajorant P data.Q (data.residueOrigin x + site)) ^ 2) ≤ L ^ (25 : ℕ) := by
  apply (data.prime_row_second_moment hB P hsub hdisjoint site).trans
  exact prime_row_moment_product_bound data.Q (fun j => primeHarmonicMass (P j)) L W
    hL hW hQ (fun j => by unfold primeHarmonicMass; positivity) hV hJ

theorem prime_row_rare_square_bound (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (P : Fin J → Finset ℕ) (hsub : ∀ j, P j ⊆ data.P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (site : ℤ)
    (L W : ℝ) (hL : 1 ≤ L) (hW : 10 ≤ W)
    (hQ : (∑ p ∈ data.Q, 1 / (p : ℝ)) ≤ Real.log L)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hJ : (J : ℝ) * (6 * W) ≤ Real.log L)
    (E : (↥(data.P ∪ data.Q) → Fin B) → Prop)
    (hE : (data.residueLaw B hB).probability E ≤
      Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ))) :
    ((data.residueLaw B hB).average (fun x =>
      primeRowMajorant P data.Q (data.residueOrigin x + site) * if E x then 1 else 0)) ^ 2 ≤
        L ^ (25 : ℕ) * Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
  apply ((data.residueLaw B hB).square_event_average_le _ E).trans
  exact mul_le_mul (data.prime_row_second_moment_polynomial hB P hsub hdisjoint site
    L W hL hW hQ hV hJ) hE
      ((data.residueLaw B hB).probability_nonneg E) (by positivity)

end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI
