import OAI.Probability.BenjaminiSchramm.NegativeMomentConvolution

namespace OAI

noncomputable section
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma signed_upper_convolution_bound (S : ℕ → ℝ) (hS : ∀ n, 0 ≤ S n)
    (β K χ : ℝ) (hβ : 0 < β) (hχ : 0 ≤ χ)
    (hbound : ∀ n, S n ≤ χ) (hmul : ∀ n j, S (n+j) ≤ S n*S j)
    (hdecay : ∀ n : ℕ, S n ≤ K*Real.exp (-(3*β/4)*n))
    (F : ℤ → ℝ≥0∞) (hF : ∀ i, F i ≤ ENNReal.ofReal χ)
    (hFpos : ∀ i : ℕ, F i ≤ ENNReal.ofReal (χ*S i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∑' i : ℤ, if i ≤ (n : ℤ) then F i*(ENNReal.ofReal (S ((n : ℤ)-i).toNat))^2 else 0) ≤
        ENNReal.ofReal (C*Real.exp (-β*n)*prefixMaximum (fun j => Real.exp (β*j)*S j) n) := by
  obtain ⟨A,hA,hpos⟩ := normalized_upper_convolution_bound S hS β K hβ hdecay
  obtain ⟨D,hD,hneg⟩ := normalized_negative_square_convolution_bound S hS β K χ hβ hχ hbound hmul hdecay
  refine ⟨χ*(A+D)+1,by positivity,fun n => ?_⟩
  let M := prefixMaximum (fun j => Real.exp (β*j)*S j) n
  have hM : 0 ≤ M := (mul_nonneg (Real.exp_pos _).le (hS 0)).trans
    (le_prefixMaximum (fun j => Real.exp (β*j)*S j) (Nat.zero_le n))
  let f (i : ℤ) : ℝ≥0∞ := if i ≤ (n : ℤ) then F i*(ENNReal.ofReal (S ((n : ℤ)-i).toNat))^2 else 0
  have hp : (∑' i : ℕ, f i) ≤ ENNReal.ofReal (χ*A*Real.exp (-β*n)*M) := by
    rw [tsum_eq_sum (s := Finset.range (n+1)) (fun i hi => ?_)]
    · calc
        _ ≤ ∑ i ∈ Finset.range (n+1), ENNReal.ofReal (χ*(S i*(S (n-i))^2)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hz : (i : ℤ) ≤ n := by exact_mod_cast hin
          have hid : ((n : ℤ)-(i : ℤ)).toNat=n-i := by omega
          dsimp only [f]
          rw [ite_eq_left hz,hid]
          calc
            _ ≤ ENNReal.ofReal (χ*S i)*(ENNReal.ofReal (S (n-i)))^2 :=
              mul_le_mul' (hFpos i) le_rfl
            _ = _ := by
              simp only [ENNReal.ofReal_mul hχ,ENNReal.ofReal_mul (hS i),
                ENNReal.ofReal_pow (hS (n-i))]
              ring
        _ = ENNReal.ofReal (χ*(∑ i ∈ Finset.range (n+1), S i*(S (n-i))^2)) := by
          rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
          intro i hi
          exact mul_nonneg hχ (mul_nonneg (hS i) (sq_nonneg _))
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by
          have hh := mul_le_mul_of_nonneg_left (hpos n) hχ
          dsimp only [M] at *
          nlinarith)
    · have hin : n < i := by
        have hh : ¬i < n+1 := by simpa only [Finset.mem_range] using hi
        omega
      have hz : ¬(i : ℤ) ≤ n := by omega
      simp only [f,ite_eq_right hz]
  have hn : (∑' j : ℕ, f (-(j+1))) ≤ ENNReal.ofReal (χ*D*Real.exp (-β*n)*M) := by
    calc
      _ ≤ ∑' j : ℕ, ENNReal.ofReal χ*ENNReal.ofReal ((S (n+(j+1)))^2) := by
        apply ENNReal.tsum_le_tsum
        intro j
        have hz : -((j : ℤ)+1) ≤ (n : ℤ) := by omega
        have hid : ((n : ℤ)-(-((j : ℤ)+1))).toNat=n+(j+1) := by omega
        dsimp only [f]
        rw [ite_eq_left hz,hid,ENNReal.ofReal_pow (hS _)]
        exact mul_le_mul' (hF _) le_rfl
      _ = ENNReal.ofReal χ*(∑' j : ℕ, ENNReal.ofReal ((S (n+(j+1)))^2)) :=
        ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal χ*(∑' j : ℕ, ENNReal.ofReal ((S (n+j))^2)) := by
        apply mul_le_mul' le_rfl
        exact ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective
          (fun j => ENNReal.ofReal ((S (n+j))^2))
      _ = ENNReal.ofReal (χ*(∑' j : ℕ, (S (n+j))^2)) := by
        rw [←ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hneg n).1,
          ENNReal.ofReal_mul hχ]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        have hh := mul_le_mul_of_nonneg_left (hneg n).2 hχ
        dsimp only [M] at *
        nlinarith)
  change (∑' i : ℤ, f i) ≤ _
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  calc
    _ ≤ ENNReal.ofReal (χ*A*Real.exp (-β*n)*M)+ENNReal.ofReal (χ*D*Real.exp (-β*n)*M) :=
      add_le_add hp hn
    _ = ENNReal.ofReal ((χ*(A+D))*Real.exp (-β*n)*M) := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      apply mul_le_mul_of_nonneg_right _ hM
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

end Percolation.BenjaminiSchramm

end

end OAI
