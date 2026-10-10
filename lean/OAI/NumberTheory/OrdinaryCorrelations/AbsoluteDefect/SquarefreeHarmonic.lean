import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MobiusInverse

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace OrdinarySelbergWeights

noncomputable def squarefreeHarmonic (z : ℕ) : ℝ :=
  ∑ a ∈ (Icc 1 z).filter Squarefree, (a : ℝ)⁻¹

theorem harmonic_le_twice_squarefree (z : ℕ) :
    (∑ n ∈ Icc 1 z, (n : ℝ)⁻¹) ≤ 2 * squarefreeHarmonic z := by
  classical
  choose b a hab hsf using exists_sq_mul_squarefree (R := ℕ)
  let g : ℕ → ℕ × ℕ := fun n => (a n, b n)
  let S := (Icc 1 z).filter Squarefree
  let T := S ×ˢ Icc 1 z
  let w : ℕ × ℕ → ℝ := fun c => (c.1 : ℝ)⁻¹ * ((c.2 : ℝ)^2)⁻¹
  have hg : ∀ n ∈ Icc 1 z, g n ∈ T := by
    intro n hn
    obtain ⟨hn1, hnz⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 < n := by omega
    have ha0 : 0 < a n := by
      have ha_ne := (hsf n).ne_zero
      exact Nat.pos_of_ne_zero ha_ne
    have hb0 : 0 < b n := by
      by_contra hb
      have hbz : b n = 0 := by omega
      have hh := hab n
      simp only [hbz, zero_pow (by omega : 2 ≠ 0), zero_mul] at hh
      omega
    have ha_le : a n ≤ n := Nat.le_of_dvd hn0 ⟨(b n)^2, by rw [Nat.mul_comm]; exact (hab n).symm⟩
    have hb_le : b n ≤ n := by
      apply Nat.le_of_dvd hn0
      refine ⟨b n * a n, ?_⟩
      rw [← mul_assoc, ← pow_two]
      exact (hab n).symm
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨ha0, ha_le.trans hnz⟩, hsf n⟩,
      Finset.mem_Icc.mpr ⟨hb0, hb_le.trans hnz⟩⟩
  have hginj : Set.InjOn g (Icc 1 z) := by
    intro n hn m hm he
    have ha : a n = a m := congrArg Prod.fst he
    have hb : b n = b m := congrArg Prod.snd he
    rw [← hab n, ← hab m, ha, hb]
  have hgsub : (Icc 1 z).image g ⊆ T := by
    intro c hc
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
    exact hg n hn
  have hw : ∀ n, w (g n) = (n : ℝ)⁻¹ := by
    intro n
    change (a n : ℝ)⁻¹ * ((b n : ℝ)^2)⁻¹ = (n : ℝ)⁻¹
    rw [← mul_inv]
    congr 1
    exact_mod_cast (by rw [mul_comm]; exact hab n : a n * (b n)^2 = n)
  have hb : (∑ j ∈ Icc 1 z, ((j : ℝ)^2)⁻¹) ≤ 2 := by
    have hset : Ioo 0 (z+1) = Icc 1 z := by ext j; simp only [mem_Ioo, mem_Icc]; omega
    simpa only [hset, Nat.cast_zero, zero_add, div_one] using
      (sum_Ioo_inv_sq_le (α := ℝ) 0 (z+1))
  calc
    _ = ∑ n ∈ Icc 1 z, w (g n) := by simp only [hw]
    _ = ∑ c ∈ (Icc 1 z).image g, w c := (Finset.sum_image hginj).symm
    _ ≤ ∑ c ∈ T, w c := Finset.sum_le_sum_of_subset_of_nonneg hgsub
      (fun _ _ _ => by dsimp [w]; positivity)
    _ = squarefreeHarmonic z * ∑ j ∈ Icc 1 z, ((j : ℝ)^2)⁻¹ := by
      simp only [T, w, Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul,
        squarefreeHarmonic, S]
    _ ≤ squarefreeHarmonic z * 2 := by
      apply mul_le_mul_of_nonneg_left hb
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    _ = _ := by ring

theorem log_le_twice_squarefreeHarmonic (z : ℕ) :
    Real.log (z + 1 : ℕ) ≤ 2 * squarefreeHarmonic z := by
  apply (log_add_one_le_harmonic z).trans
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
    harmonic_le_twice_squarefree z

theorem nu_le_selbergTerms (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    s.nu d ≤ s.selbergTerms d := by
  rw [s.selbergTerms_apply]
  apply le_mul_of_one_le_right (s.nu_pos_of_dvd_prodPrimes hd).le
  apply Finset.one_le_prod₀
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpd := (Nat.dvd_of_mem_primeFactors hp).trans hd
  apply (one_le_inv₀ (sub_pos.mpr (s.nu_lt_one_of_prime p hpprime hpd))).mpr
  linarith [s.nu_pos_of_prime p hpprime hpd]

theorem squarefree_dvd_of_primes {P z d : ℕ} (hP : P ≠ 0)
    (hpr : ∀ p, Nat.Prime p → p ≤ z → p ∣ P) (hd : Squarefree d) (hdz : d ≤ z) :
    d ∣ P := by
  rw [← Nat.prod_primeFactors_of_squarefree hd, Nat.prod_primeFactors_dvd_iff hP]
  intro p hp
  have hppr := Nat.prime_of_mem_primeFactors hp
  exact Nat.mem_primeFactors.mpr ⟨hppr, hpr p hppr
    ((Nat.le_of_dvd (Nat.pos_of_ne_zero hd.ne_zero)
      (Nat.dvd_of_mem_primeFactors hp)).trans hdz), hP⟩

theorem squarefreeHarmonic_le_mass (s : BoundingSieve) (z : ℕ)
    (hpr : ∀ p, Nat.Prime p → p ≤ z → p ∣ s.prodPrimes)
    (hnu : ∀ d, d ∣ s.prodPrimes → (d : ℝ)⁻¹ ≤ s.nu d) :
    squarefreeHarmonic z ≤ mass s z := by
  unfold squarefreeHarmonic mass
  rw [← Finset.sum_filter]
  have hsub : (Icc 1 z).filter Squarefree ⊆ s.prodPrimes.divisors.filter (· ≤ z) := by
    intro d hd
    obtain ⟨hdI, hdsf⟩ := Finset.mem_filter.mp hd
    have hdz := (Finset.mem_Icc.mp hdI).2
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨squarefree_dvd_of_primes s.prodPrimes_ne_zero hpr hdsf hdz, s.prodPrimes_ne_zero⟩, hdz⟩
  calc
    _ ≤ ∑ d ∈ (Icc 1 z).filter Squarefree, s.selbergTerms d := by
      apply Finset.sum_le_sum
      intro d hd
      have hdp := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp (hsub hd)).1
      exact (hnu d hdp).trans (nu_le_selbergTerms s hdp)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun d hd _ => (s.selbergTerms_pos
        (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)).le)

theorem log_le_twice_mass (s : BoundingSieve) (z : ℕ)
    (hpr : ∀ p, Nat.Prime p → p ≤ z → p ∣ s.prodPrimes)
    (hnu : ∀ d, d ∣ s.prodPrimes → (d : ℝ)⁻¹ ≤ s.nu d) :
    Real.log (z + 1 : ℕ) ≤ 2 * mass s z := by
  exact (log_le_twice_squarefreeHarmonic z).trans
    (mul_le_mul_of_nonneg_left (squarefreeHarmonic_le_mass s z hpr hnu) (by norm_num))

end OrdinarySelbergWeights

end

end OAI
