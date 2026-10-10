import OAI.NumberTheory.TotientAsymptotic.OmegaReciprocal

namespace OAI

/-! A concrete Rankin moment for the smooth cofactor discarded in extraction. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def powerReciprocal (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ)^σ/(n : ℝ)
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n),mul_div_mul_comm]

lemma powerReciprocal_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ powerReciprocal σ n := by
  change 0 ≤ (n : ℝ)^σ/(n : ℝ)
  positivity

lemma powerReciprocal_prime_norm {σ : ℝ} (hσ : σ < 1) {p : ℕ} (hp : p.Prime) :
    ‖powerReciprocal σ p‖ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [Real.norm_eq_abs,abs_of_nonneg (powerReciprocal_nonneg σ p)]
  change (p : ℝ)^σ/(p : ℝ) < 1
  rw [div_lt_one (zero_lt_one.trans hp1)]
  simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hp1 hσ

lemma powerReciprocal_euler_factor {σ : ℝ} (hσ : σ < 1) {p : ℕ} (hp : p.Prime)
    (hpow : (p : ℝ)^σ ≤ 3/2) :
    (1-powerReciprocal σ p)⁻¹ ≤ ((p : ℝ)/(p-1))^3 := by
  have hnorm := powerReciprocal_prime_norm hσ hp
  rw [Real.norm_eq_abs,abs_of_nonneg (powerReciprocal_nonneg σ p)] at hnorm
  have hb : powerReciprocal σ p ≤ omegaReciprocal p := by
    rw [omegaReciprocal_prime hp]
    exact div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)
  have hω := omegaReciprocal_prime_norm hp
  rw [Real.norm_eq_abs,abs_of_nonneg (omegaReciprocal_nonneg p)] at hω
  have hh := one_div_le_one_div_of_le (by linarith : 0 < 1-omegaReciprocal p)
    (sub_le_sub_left hb 1)
  rw [one_div,one_div] at hh
  exact hh.trans (omega_euler_factor_le hp)

lemma smooth_power_reciprocal_mass {σ : ℝ} (hσ : σ < 1) (N : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N)
    (hpow : ∀ p : ℕ, p.Prime → p ≤ N → (p : ℝ)^σ ≤ 3/2) :
    (∑ n ∈ Q, powerReciprocal σ n) ≤ (primeEulerProduct N)^3 := by
  classical
  let S := Finset.Icc 2 N
  have hm (n : ℕ) (hn : n ∈ Q) : n ∈ Nat.factoredNumbers S := by
    refine ⟨(hQ n hn).1.ne',?_⟩
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactorsList hp).two_le,
      (primeFactor_le_largest hp).trans (hQ n hn).2⟩
  let e : {n // n ∈ Q} → Nat.factoredNumbers S := fun n => ⟨n.1,hm n.1 n.2⟩
  let T : Finset (Nat.factoredNumbers S) := Q.attach.image e
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers S => z.val) h
  have hsum : (∑ n ∈ Q, powerReciprocal σ n) = ∑ n ∈ T, powerReciprocal σ n := by
    dsimp only [T]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    exact (Finset.sum_attach Q (fun n : ℕ => powerReciprocal σ n)).symm
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := powerReciprocal σ) (fun {_} hp => powerReciprocal_prime_norm hσ hp) S
  calc
    _ = ∑ n ∈ T, powerReciprocal σ n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S, powerReciprocal σ n :=
      hs.1.of_norm.sum_le_tsum T (fun n _ => powerReciprocal_nonneg σ n)
    _ = ∏ p ∈ S with p.Prime, (1-powerReciprocal σ p)⁻¹ := hs.2.tsum_eq
    _ ≤ ∏ p ∈ S with p.Prime, ((p : ℝ)/(p-1))^3 := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hh := powerReciprocal_prime_norm hσ (Finset.mem_filter.mp hp).2
        rw [Real.norm_eq_abs,abs_of_nonneg (powerReciprocal_nonneg σ p)] at hh
        exact inv_nonneg.mpr (by linarith)
      · intro p hp
        exact powerReciprocal_euler_factor hσ (Finset.mem_filter.mp hp).2
          (hpow p (Finset.mem_filter.mp hp).2 (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2)
    _ = _ := by rw [Finset.prod_pow]; rfl

lemma totient_ratio_le_eulerProduct_of_smooth {n N : ℕ} (hn : 0 < n)
    (hs : largestPrimeFactor n ≤ N) : (n : ℝ)/n.totient ≤ primeEulerProduct N := by
  rw [totient_ratio_product hn]
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hprime.two_le,
      (primeFactor_le_largest ((Nat.mem_primeFactorsList_iff_dvd hn.ne' hprime).mpr
        (Nat.dvd_of_mem_primeFactors hp))).trans hs⟩,hprime⟩
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · intro p hp _
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < p-1)).mpr
    linarith

lemma quarter_log_power {N p : ℕ} (hN : 2 ≤ N) (hp : p.Prime) (hpN : p ≤ N) :
    (p : ℝ)^(1/(4*Real.log N)) ≤ 3/2 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl := Real.log_le_log hp0 (show (p : ℝ) ≤ N by exact_mod_cast hpN)
  rw [Real.rpow_def_of_pos hp0]
  have hexp : Real.exp (1/4 : ℝ) ≤ 3/2 := by
    have hh := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) < 1)
    norm_num at hh
    linarith
  apply (Real.exp_le_exp.mpr ?_).trans hexp
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*Real.log N)).mpr
  convert hl using 1
  ring

lemma quarter_log_exponent_lt_one {N : ℕ} (hN : 2 ≤ N) : 1/(4*Real.log N) < (1 : ℝ) := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ)<2) (show (2 : ℝ) ≤ N by exact_mod_cast hN)
  have hlog2 := Real.log_two_gt_d9
  apply (div_lt_one (by nlinarith : (0 : ℝ)<4*Real.log N)).mpr
  nlinarith

/-- A coarse fourth power of the Mertens product suffices for the tail;
no asymptotic estimate for smooth integers is assumed. -/
theorem smooth_cofactor_power_mass {N : ℕ} (hN : 2 ≤ N) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N) :
    (∑ n ∈ Q, (n : ℝ)^(1/(4*Real.log N))/(n.totient : ℝ)) ≤ (primeEulerProduct N)^4 := by
  let σ := 1/(4*Real.log N)
  have hE : 0 ≤ primeEulerProduct N := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  calc
    _ ≤ primeEulerProduct N*∑ n ∈ Q, powerReciprocal σ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ)<n := by exact_mod_cast (hQ n hn).1
      have hb := mul_le_mul_of_nonneg_right
        (totient_ratio_le_eulerProduct_of_smooth (hQ n hn).1 (hQ n hn).2)
        (powerReciprocal_nonneg σ n)
      convert hb using 1
      dsimp [powerReciprocal,σ]
      field_simp
    _ ≤ primeEulerProduct N*(primeEulerProduct N)^3 :=
      mul_le_mul_of_nonneg_left
        (smooth_power_reciprocal_mass (quarter_log_exponent_lt_one hN) N Q hQ
          (fun p hp hpN => quarter_log_power hN hp hpN)) hE
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
