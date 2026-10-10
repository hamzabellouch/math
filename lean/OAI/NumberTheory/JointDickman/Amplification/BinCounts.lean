import OAI.NumberTheory.JointDickman.Amplification.BinLabels
import OAI.NumberTheory.JointDickman.Basic

namespace OAI

/-!
# Bounded multiplicity counts and smoothness at bin endpoints

A product of the prime powers counted in a bin divides the integer. This
bounds every bin count uniformly on fixed windows `n ≤ C*x`. The endpoint
criterion identifies smoothness with vanishing counts in all higher bins.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem mem_primeBin_iff {x : ℝ} (hx : 0 ≤ x) (J k p : ℕ) :
    p ∈ primeBin x J k ↔ p.Prime ∧
      x ^ ((k : ℝ) / J) < (p : ℝ) ∧ (p : ℝ) ≤ x ^ (((k : ℝ) + 1) / J) := by
  classical
  simp only [primeBin, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hl, hu⟩, hp⟩
    exact ⟨hp, Nat.lt_of_floor_lt hl,
      (Nat.le_floor_iff (Real.rpow_nonneg hx _)).mp hu⟩
  · rintro ⟨hp, hl, hu⟩
    exact ⟨⟨(Nat.floor_lt (Real.rpow_nonneg hx _)).mpr hl,
      (Nat.le_floor_iff (Real.rpow_nonneg hx _)).mpr hu⟩, hp⟩

/-- The product of the complete prime powers selected by a finite bin divides `n`. -/
theorem bin_primePower_prod_dvd (E : Finset ℕ) (n : ℕ) :
    (∏ p ∈ E, p ^ n.factorization p) ∣ n := by
  classical
  let f : ℕ →₀ ℕ := n.factorization.filter (fun p => p ∈ E)
  have hf : f ≤ n.factorization := by
    intro p
    simp only [f, Finsupp.filter_apply]
    split_ifs <;> simp
  have hsupp : f.support ⊆ E := by
    intro p hp
    exact (Finset.mem_filter.mp (show p ∈ n.factorization.support.filter (fun p => p ∈ E) from hp)).2
  have heq : f.prod (fun p a => p ^ a) = ∏ p ∈ E, p ^ n.factorization p := by
    rw [Finsupp.prod_of_support_subset f hsupp _ (by simp)]
    apply Finset.prod_congr rfl
    intro p hp
    simp only [f, Finsupp.filter_apply, ite_eq_left hp]
  rw [← heq]
  exact Nat.prod_pow_dvd_of_le_factorization hf

/-- A lower bound for every counted prime gives a power lower bound for `n`. -/
theorem binCount_pow_le (E : Finset ℕ) {n : ℕ} (hn : n ≠ 0)
    {q : ℝ} (hq : 0 ≤ q) (hE : ∀ p ∈ E, q ≤ (p : ℝ)) :
    q ^ binCount E n ≤ (n : ℝ) := by
  calc
    q ^ binCount E n = ∏ p ∈ E, q ^ n.factorization p :=
      (Finset.prod_pow_eq_pow_sum E n.factorization q).symm
    _ ≤ ∏ p ∈ E, (p : ℝ) ^ n.factorization p :=
      Finset.prod_le_prod₀ (fun p _ => pow_nonneg hq _)
        (fun p hp => pow_le_pow_left₀ hq (hE p hp) _)
    _ = ((∏ p ∈ E, p ^ n.factorization p : ℕ) : ℝ) := by norm_cast
    _ ≤ n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (bin_primePower_prod_dvd E n)

/-- Uniform boundedness of every relevant count, sufficient for interpolation.
The bound holds simultaneously for all bin indices `k ≥ 1`. -/
theorem primeBin_count_eventually_le (J : ℕ) (hJ : 0 < J) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ≤ C * x → binCount (primeBin x J k) n ≤ J := by
  have hJreal : (0 : ℝ) < J := by exact_mod_cast hJ
  have hroot := (tendsto_rpow_atTop (div_pos zero_lt_one hJreal)).eventually
    (eventually_gt_atTop C)
  filter_upwards [hroot, eventually_ge_atTop (1 : ℝ)] with x hxC hxone
  intro k hk n hn hnupper
  let q : ℝ := x ^ ((1 : ℝ) / J)
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hxone
  have hq : 1 ≤ q := Real.one_le_rpow hxone (div_nonneg zero_le_one hJreal.le)
  have hprimes : ∀ p ∈ primeBin x J k, q ≤ (p : ℝ) := by
    intro p hp
    have hl := ((mem_primeBin_iff hxpos.le J k p).mp hp).2.1
    have hexp : (1 : ℝ) / J ≤ (k : ℝ) / J :=
      div_le_div_of_nonneg_right (by exact_mod_cast hk) hJreal.le
    exact (Real.rpow_le_rpow_of_exponent_le hxone hexp).trans hl.le
  have hpow := binCount_pow_le (primeBin x J k) (by omega : n ≠ 0) (le_trans zero_le_one hq) hprimes
  have hrootpow : q ^ J = x := by
    simpa only [q, one_div] using Real.rpow_inv_natCast_pow hxpos.le (by omega : J ≠ 0)
  by_contra hcount
  have hjcount : J + 1 ≤ binCount (primeBin x J k) n := by omega
  have hmon := pow_le_pow_right₀ hq hjcount
  have hbig : C * x < q ^ (J + 1) := by
    rw [pow_succ, hrootpow]
    dsimp [q] at hxC ⊢
    nlinarith
  linarith

/-- A finite sequence crossing a level has an adjacent pair straddling it. -/
private theorem exists_adjacent_crossing (y : ℕ → ℝ) (a : ℝ) {d : ℕ}
    (hzero : y 0 < a) (hend : a ≤ y d) :
    ∃ k : ℕ, k < d ∧ y k < a ∧ a ≤ y (k + 1) := by
  induction d with
  | zero => exact False.elim (not_lt_of_ge hend hzero)
  | succ d ih =>
    by_cases hd : a ≤ y d
    · obtain ⟨k, hk, hl, hu⟩ := ih hd
      exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self d), hl, hu⟩
    · exact ⟨d, Nat.lt_succ_self d, lt_of_not_ge hd, hend⟩

/-- Every number between a bin endpoint and `x` belongs to a higher bin. -/
theorem exists_higher_primeBin {x : ℝ} (hx : 0 ≤ x) {J r p : ℕ}
    (hJ : 0 < J) (hr : r ≤ J) (hp : p.Prime)
    (hlow : x ^ ((r : ℝ) / J) < (p : ℝ)) (hhigh : (p : ℝ) ≤ x) :
    ∃ k ∈ Finset.Ico r J, p ∈ primeBin x J k := by
  let y : ℕ → ℝ := fun i => x ^ (((r + i : ℕ) : ℝ) / J)
  have hzero : y 0 < (p : ℝ) := by simpa only [y, Nat.add_zero] using hlow
  have hend : (p : ℝ) ≤ y (J - r) := by
    have hindices : r + (J - r) = J := by omega
    change (p : ℝ) ≤ x ^ (((r + (J - r) : ℕ) : ℝ) / J)
    rw [hindices, div_self (by exact_mod_cast (Nat.ne_of_gt hJ) : (J : ℝ) ≠ 0),
      Real.rpow_one]
    exact hhigh
  obtain ⟨i, hi, hlo, hhi⟩ := exists_adjacent_crossing y (p : ℝ) hzero hend
  refine ⟨r + i, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
  apply (mem_primeBin_iff hx J (r + i) p).mpr
  refine ⟨hp, hlo, ?_⟩
  simpa only [y, Nat.cast_add, Nat.cast_one, add_assoc] using hhi

/-- Smoothness at a rational endpoint is exactly vanishing of the higher-bin
multiplicity counts, provided `1 ≤ n ≤ x`. -/
theorem maxPrimeFac_le_iff_higher_counts_zero {x : ℝ} (hx : 1 ≤ x)
    {J r n : ℕ} (hJ : 0 < J) (hr : r ≤ J) (hn : 1 ≤ n) (hnx : (n : ℝ) ≤ x) :
    (n.maxPrimeFac : ℝ) ≤ x ^ ((r : ℝ) / J) ↔
      ∀ k ∈ Finset.Ico r J, binCount (primeBin x J k) n = 0 := by
  have hnzero : n ≠ 0 := by omega
  have hxzero : 0 ≤ x := le_trans zero_le_one hx
  constructor
  · intro hsmooth k hk
    apply binCount_eq_zero_of_no_factor
    intro p hp hpdiv
    obtain ⟨hpprime, hplower, _⟩ := (mem_primeBin_iff hxzero J k p).mp hp
    have hpmax : (p : ℝ) ≤ n.maxPrimeFac := by
      exact_mod_cast Nat.le_maxPrimeFac hnzero hpprime hpdiv
    have hexp : (r : ℝ) / J ≤ (k : ℝ) / J :=
      div_le_div_of_nonneg_right (by exact_mod_cast (Finset.mem_Ico.mp hk).1) (Nat.cast_nonneg _)
    have hpower := Real.rpow_le_rpow_of_exponent_le hx hexp
    linarith
  · intro hcounts
    by_cases hone : n = 1
    · subst n
      simpa using Real.one_le_rpow hx (div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg J))
    by_contra hsmooth
    have hpprime := Nat.prime_maxPrimeFac_of_one_lt (show 1 < n by omega)
    have hpupper : (n.maxPrimeFac : ℝ) ≤ x := by
      have hpn : (n.maxPrimeFac : ℝ) ≤ n := by exact_mod_cast Nat.maxPrimeFac_le (n := n)
      exact hpn.trans hnx
    obtain ⟨k, hk, hpmem⟩ := exists_higher_primeBin hxzero hJ hr hpprime
      (lt_of_not_ge hsmooth) hpupper
    have hpcount : 0 < n.factorization n.maxPrimeFac :=
      hpprime.factorization_pos_of_dvd hnzero Nat.maxPrimeFac_dvd
    have hle : n.factorization n.maxPrimeFac ≤ binCount (primeBin x J k) n :=
      Finset.single_le_sum (fun p _ => Nat.zero_le (n.factorization p)) hpmem
    rw [hcounts k hk] at hle
    omega


/-- The fixed coefficient vector from interpolation works on every fixed
window `n ≤ C*x`, once the scale is sufficiently large. -/
theorem centered_binLabel_interpolation_on_window {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (ζ : ι → ℂ) (μ : ℂ) (C : ℝ) :
    ∃ c : (ι → Fin (J + 1)) → ℂ, ∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ C * x →
        binLabel (fun i => primeBin x J (k i)) ζ n - μ =
          ∑ a : ι → Fin (J + 1), c a *
            (binLabel (fun i => primeBin x J (k i))
              (fun i => interpolationNode (a i)) n : ℂ) := by
  obtain ⟨c, hc⟩ := centered_binLabel_interpolation ζ μ J
  refine ⟨c, ?_⟩
  filter_upwards [primeBin_count_eventually_le J hJ C] with x hx n hn hnupper
  exact hc _ n (by omega) (fun i => hx (k i) (hk i) n hn hnupper)

end JointDickman

end OAI
