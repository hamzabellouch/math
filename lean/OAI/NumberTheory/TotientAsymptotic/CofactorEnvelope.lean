import OAI.NumberTheory.TotientAsymptotic.CofactorMass

namespace OAI

/-!
The cofactor envelope from Mertens' published prime-product theorem.
We use only its upper bound, stated as Theorem 1.1, equation (1.2), in
J. D. Lichtman, *Mertens' prime product formula, dissected*,
arXiv:2002.03361v3 (2021), citing Mertens (1874),
*J. reine angew. Math.* 78, 46–62. This is an explicit conditional input.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def primeEulerProduct (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime, (p : ℝ)/(p-1)

def MertensProductInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → primeEulerProduct N ≤ C*Real.log N

lemma totient_ratio_product {n : ℕ} (hn : 0 < n) :
    (n : ℝ)/n.totient = ∏ p ∈ n.primeFactors, (p : ℝ)/(p-1) := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hprod : (0 : ℝ) < ∏ p ∈ n.primeFactors, (p-1 : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have hh : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    linarith
  have he := congrArg (fun k : ℕ => (k : ℝ)) (Nat.totient_mul_prod_primeFactors n)
  push_cast at he
  have he' : (n.totient : ℝ)*(∏ p ∈ n.primeFactors, (p : ℝ)) =
      n*(∏ p ∈ n.primeFactors, (p-1 : ℝ)) := by
    convert he using 1
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
  rw [Finset.prod_div_distrib]
  exact (div_eq_div_iff hφ.ne' hprod.ne').mpr (by nlinarith [he'])

lemma totient_ratio_le_eulerProduct {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (n : ℝ)/n.totient ≤ primeEulerProduct N := by
  rw [totient_ratio_product hn]
  unfold primeEulerProduct
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hprime.two_le, (Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)).trans hnN⟩, hprime⟩
  · intro p hp
    have hpos : (0 : ℝ) < p-1 := by
      have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      linarith
    exact div_nonneg (Nat.cast_nonneg _) hpos.le
  · intro p hp _
    have hprime := (Finset.mem_filter.mp hp).2
    have hpos : (0 : ℝ) < p-1 := by
      have : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
      linarith
    apply (le_div_iff₀ hpos).mpr
    linarith

/-- A deliberately coarse logarithmic-square envelope is sufficient for the
small discrete cofactor. It avoids imposing any coprimality restrictions. -/
theorem sum_reciprocal_totient_le (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (n.totient : ℝ)⁻¹) ≤
        C*Real.log N*(1+Real.log N) := by
  obtain ⟨C, hC, hprod⟩ := hmertens
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (n.totient : ℝ)⁻¹ ≤ C*Real.log N*(n : ℝ)⁻¹ := by
    have hn' := Finset.mem_Icc.mp hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn'.1
    have hb := (totient_ratio_le_eulerProduct hn'.1 hn'.2).trans (hprod N hN)
    have hh := mul_le_mul_of_nonneg_right hb (inv_pos.mpr hnR).le
    convert hh using 1
    all_goals field_simp
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, C*Real.log N*(n : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = C*Real.log N*∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ C*Real.log N*(1+Real.log N) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hlog)
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        using harmonic_le_one_add_log N

end TotientAsymptotic

end

end OAI
