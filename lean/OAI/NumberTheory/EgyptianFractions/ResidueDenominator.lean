import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.ResidueConstruction

/-- A binary factor can cover any positive cutoff at a logarithmic cost of at most `log 2`. -/
theorem exists_binary_factor {x : ℝ} (hx : 1 ≤ x) :
    ∃ a : ℕ, x ≤ (2 : ℝ) ^ a ∧ (2 : ℝ) ^ a ≤ 2 * x ∧
      (a : ℝ) * Real.log 2 ≤ Real.log x + Real.log 2 := by
  obtain ⟨n, hn, hnx⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  have hxpos : 0 < x := by linarith
  have hpow : (2 : ℝ) ^ (n + 1) ≤ 2 * x := by
    rw [pow_succ]
    nlinarith
  refine ⟨n + 1, hnx.le, hpow, ?_⟩
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (n + 1)) hpow
  rw [Real.log_pow, Real.log_mul (by norm_num) (ne_of_gt hxpos)] at hlog
  linarith

theorem exists_binary_cutoff {S : ℝ} (hS : 1 ≤ S) (D : ℕ) :
    ∃ a : ℕ, S ^ D ≤ (2 : ℝ) ^ a ∧
      (a : ℝ) * Real.log 2 ≤ (D : ℝ) * Real.log S + Real.log 2 := by
  obtain ⟨a, ha, _, hlog⟩ := exists_binary_factor (one_le_pow₀ hS)
  refine ⟨a, ha, ?_⟩
  simpa only [Real.log_pow] using hlog

/-- The auxiliary denominator from one fixed block and a family of paired blocks. -/
def auxiliaryDenominator {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) : ℕ :=
  2 ^ a * (∏ j, p j) * ∏ i, ∏ j, ∏ e, q i j e

/-- The fixed block enumerates all subset products. -/
def subsetEntry {m : ℕ} (p : Fin m → ℕ) (I : Fin m → Fin 2) : ℕ :=
  ∏ j, p j ^ (I j).val

/-- A paired block selects exactly one entry from every pair. -/
def pairedEntry {m : ℕ} (q : Fin m → Fin 2 → ℕ) (I : Fin m → Fin 2) : ℕ :=
  ∏ j, q j (I j)

theorem subsetEntry_dvd_product {m : ℕ} (p : Fin m → ℕ) (I : Fin m → Fin 2) :
    subsetEntry p I ∣ ∏ j, p j := by
  apply Finset.prod_dvd_prod_of_dvd
  intro j hj
  have hI : (I j).val = 0 ∨ (I j).val = 1 := by omega
  rcases hI with hI | hI <;> simp [hI]

/-- A selected prime divides a fixed-block entry precisely when its bit is one. -/
theorem prime_dvd_subsetEntry_iff {m : ℕ} (p : Fin m → ℕ)
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (I : Fin m → Fin 2) (j : Fin m) :
    p j ∣ subsetEntry p I ↔ (I j).val = 1 := by
  constructor
  · intro h
    obtain ⟨k, hk, hdiv⟩ :=
      ((Nat.prime_iff.mp (hp j)).dvd_finsetProd_iff (fun k => p k ^ (I k).val)).mp h
    have hjk : j = k := hinj (Nat.prime_eq_prime_of_dvd_pow (hp j) (hp k) hdiv)
    subst k
    have hI : (I j).val = 0 ∨ (I j).val = 1 := by omega
    rcases hI with hI | hI
    · simp only [hI, pow_zero] at hdiv
      exact False.elim ((hp j).not_dvd_one hdiv)
    · exact hI
  · intro hI
    apply dvd_trans (show p j ∣ p j ^ (I j).val by simp [hI])
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)

/-- Distinct primes give all `2^m` fixed-block entries distinct. -/
theorem subsetEntry_injective {m : ℕ} (p : Fin m → ℕ)
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p) :
    Function.Injective (subsetEntry p) := by
  intro I J hIJ
  funext j
  apply Fin.ext
  have hiff : (I j).val = 1 ↔ (J j).val = 1 := by
    rw [← prime_dvd_subsetEntry_iff p hp hinj I j,
      ← prime_dvd_subsetEntry_iff p hp hinj J j, hIJ]
  have hi := (I j).isLt
  have hj := (J j).isLt
  omega

theorem subsetEntry_image_card {m : ℕ} (p : Fin m → ℕ)
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p) :
    (Finset.univ.image (subsetEntry p)).card = 2 ^ m := by
  rw [Finset.card_image_of_injective _ (subsetEntry_injective p hp hinj)]
  simp

theorem pairedEntry_dvd_product {m : ℕ} (q : Fin m → Fin 2 → ℕ)
    (I : Fin m → Fin 2) : pairedEntry q I ∣ ∏ j, ∏ e, q j e := by
  apply Finset.prod_dvd_prod_of_dvd
  intro j hj
  exact Finset.dvd_prod_of_mem (q j) (Finset.mem_univ (I j))

theorem binary_factor_dvd_auxiliary {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) :
    2 ^ a ∣ auxiliaryDenominator a p q := by
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

/-- Any covering binary factor also contains the precise ceiling cutoff used by terminal descent. -/
theorem ceiling_binary_factor_dvd_auxiliary {m R : ℕ} (a D : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) {S : ℝ} (hS : 0 < S)
    (hcut : S ^ D ≤ (2 : ℝ) ^ a) :
    2 ^ ⌈(D : ℝ) * Real.log S / Real.log 2⌉₊ ∣ auxiliaryDenominator a p q := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (pow_pos hS D) hcut
  rw [Real.log_pow, Real.log_pow] at hlog
  have hceil : ⌈(D : ℝ) * Real.log S / Real.log 2⌉₊ ≤ a := by
    apply Nat.ceil_le.mpr
    exact (div_le_iff₀ hlog2).mpr hlog
  exact (pow_dvd_pow 2 hceil).trans (binary_factor_dvd_auxiliary a p q)

theorem subsetEntry_dvd_auxiliary {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (I : Fin m → Fin 2) :
    subsetEntry p I ∣ auxiliaryDenominator a p q := by
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (subsetEntry_dvd_product p I) _) _

theorem pairedEntry_dvd_auxiliary {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (i : Fin R) (I : Fin m → Fin 2) :
    pairedEntry (q i) I ∣ auxiliaryDenominator a p q := by
  apply dvd_mul_of_dvd_right
  exact (pairedEntry_dvd_product (q i) I).trans
    (Finset.dvd_prod_of_mem (fun i => ∏ j, ∏ e, q i j e) (Finset.mem_univ i))

theorem auxiliaryDenominator_pos {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) : 0 < auxiliaryDenominator a p q := by
  unfold auxiliaryDenominator
  apply Nat.mul_pos
  · exact Nat.mul_pos (by positivity) (Finset.prod_pos (fun j _ => hp j))
  · exact Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ =>
      Finset.prod_pos (fun e _ => hq i j e)))

theorem subsetEntry_pos {m : ℕ} (p : Fin m → ℕ) (hp : ∀ j, 0 < p j)
    (I : Fin m → Fin 2) : 0 < subsetEntry p I := by
  exact Finset.prod_pos (fun j _ => pow_pos (hp j) _)

theorem pairedEntry_pos {m : ℕ} (q : Fin m → Fin 2 → ℕ)
    (hq : ∀ j e, 0 < q j e) (I : Fin m → Fin 2) : 0 < pairedEntry q I := by
  exact Finset.prod_pos (fun j _ => hq j (I j))

private theorem log_nat_product {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (hf : ∀ i, 0 < f i) :
    Real.log ((∏ i, f i : ℕ) : ℝ) = ∑ i, Real.log (f i : ℝ) := by
  rw [Nat.cast_prod, Real.log_prod]
  intro i hi
  exact_mod_cast (Nat.ne_of_gt (hf i))

theorem log_auxiliaryDenominator {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) :
    Real.log (auxiliaryDenominator a p q : ℝ) =
      (a : ℝ) * Real.log 2 + (∑ j, Real.log (p j : ℝ)) +
        ∑ i, ∑ j, ∑ e, Real.log (q i j e : ℝ) := by
  have hP : (0 : ℝ) < (∏ j, p j : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun j _ => hp j)
  have hQ : (0 : ℝ) < (∏ i, ∏ j, ∏ e, q i j e : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ =>
      Finset.prod_pos (fun e _ => hq i j e)))
  have hqi : ∀ i, 0 < ∏ j, ∏ e, q i j e := fun i =>
    Finset.prod_pos (fun j _ => Finset.prod_pos (fun e _ => hq i j e))
  have hqj : ∀ i j, 0 < ∏ e, q i j e := fun i j =>
    Finset.prod_pos (fun e _ => hq i j e)
  have hlogQ : Real.log ((∏ i, ∏ j, ∏ e, q i j e : ℕ) : ℝ) =
      ∑ i, ∑ j, ∑ e, Real.log (q i j e : ℝ) := by
    rw [log_nat_product _ hqi]
    apply Finset.sum_congr rfl
    intro i hi
    rw [log_nat_product _ (hqj i)]
    apply Finset.sum_congr rfl
    intro j hj
    exact log_nat_product _ (hq i j)
  unfold auxiliaryDenominator
  rw [Nat.cast_mul, Nat.cast_mul,
    Real.log_mul (mul_ne_zero (by positivity) (ne_of_gt hP)) (ne_of_gt hQ),
    Real.log_mul (by positivity) (ne_of_gt hP), Nat.cast_pow, Real.log_pow,
    log_nat_product p hp, hlogQ]
  norm_num

/-- The precise logarithmic size budget counts one fixed block and two factors per pair. -/
theorem log_auxiliaryDenominator_le {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) (U : ℝ)
    (hpU : ∀ j, Real.log (p j : ℝ) ≤ U)
    (hqU : ∀ i j e, Real.log (q i j e : ℝ) ≤ U) :
    Real.log (auxiliaryDenominator a p q : ℝ) ≤
      (a : ℝ) * Real.log 2 + (2 * (R : ℝ) + 1) * (m : ℝ) * U := by
  have hP : (∑ j, Real.log (p j : ℝ)) ≤ (m : ℝ) * U := by
    calc
      _ ≤ ∑ _j : Fin m, U := Finset.sum_le_sum (fun j _ => hpU j)
      _ = (m : ℝ) * U := by simp
  have hQ : (∑ i, ∑ j, ∑ e, Real.log (q i j e : ℝ)) ≤
      2 * (R : ℝ) * (m : ℝ) * U := by
    calc
      _ ≤ ∑ _i : Fin R, ∑ _j : Fin m, ∑ _e : Fin 2, U := by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          Finset.sum_le_sum (fun e _ => hqU i j e)))
      _ = 2 * (R : ℝ) * (m : ℝ) * U := by simp; ring
  rw [log_auxiliaryDenominator a p q hp hq]
  nlinarith

theorem log_auxiliaryDenominator_ge {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) (L : ℝ)
    (hpL : ∀ j, L ≤ Real.log (p j : ℝ)) :
    (m : ℝ) * L ≤ Real.log (auxiliaryDenominator a p q : ℝ) := by
  have hP : (m : ℝ) * L ≤ ∑ j, Real.log (p j : ℝ) := by
    calc
      _ = ∑ _j : Fin m, L := by simp
      _ ≤ ∑ j, Real.log (p j : ℝ) := Finset.sum_le_sum (fun j _ => hpL j)
  have hQ : 0 ≤ ∑ i, ∑ j, ∑ e, Real.log (q i j e : ℝ) := by
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun e _ => Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ q i j e from hq i j e)))))
  have ha : 0 ≤ (a : ℝ) * Real.log 2 := by positivity
  rw [log_auxiliaryDenominator a p q hp hq]
  linarith

theorem log_pairedEntry_le {m : ℕ} (q : Fin m → Fin 2 → ℕ)
    (hq : ∀ j e, 0 < q j e) (I : Fin m → Fin 2) (U : ℝ)
    (hqU : ∀ j e, Real.log (q j e : ℝ) ≤ U) :
    Real.log (pairedEntry q I : ℝ) ≤ (m : ℝ) * U := by
  rw [pairedEntry, log_nat_product _ (fun j => hq j (I j))]
  calc
    _ ≤ ∑ _j : Fin m, U := Finset.sum_le_sum (fun j _ => hqU j (I j))
    _ = (m : ℝ) * U := by simp

theorem log_subsetEntry_le {m : ℕ} (p : Fin m → ℕ) (hp : ∀ j, 0 < p j)
    (I : Fin m → Fin 2) (U : ℝ) (hU : 0 ≤ U)
    (hpU : ∀ j, Real.log (p j : ℝ) ≤ U) :
    Real.log (subsetEntry p I : ℝ) ≤ (m : ℝ) * U := by
  rw [subsetEntry, log_nat_product _ (fun j => pow_pos (hp j) _)]
  calc
    _ ≤ ∑ _j : Fin m, U := by
      apply Finset.sum_le_sum
      intro j hj
      have hI : (I j).val = 0 ∨ (I j).val = 1 := by omega
      rcases hI with hI | hI
      · simpa [hI] using hU
      · simpa [hI] using hpU j
    _ = (m : ℝ) * U := by simp

/-- The numerical budgets have ample uniform slack.
The floor-scale estimates are supplied separately, so this is pure algebra. -/
theorem residue_size_budget {S : ℝ} {m a : ℕ}
    (hlog : 1 ≤ Real.log S) (hlarge : 100 * Real.log S ≤ S)
    (hmLower : S - Real.log S ≤ (m : ℝ) * Real.log S)
    (hmUpper : (m : ℝ) * Real.log S ≤ S)
    (ha : (a : ℝ) * Real.log 2 ≤ 100000 * Real.log S + Real.log 2) :
    S < (m : ℝ) * (100 * Real.log S) ∧
      (a : ℝ) * Real.log 2 + (2 * (1000 : ℝ) + 1) * (m : ℝ) *
        (100 * Real.log S + Real.log 2) ≤ 204204 * S ∧
      (m : ℝ) * (100 * Real.log S + Real.log 2) ≤ 101 * S := by
  have htwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hmpos : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm : (m : ℝ) ≤ S := by
    have := mul_le_mul_of_nonneg_left hlog hmpos
    nlinarith
  have hm2 : (m : ℝ) * Real.log 2 ≤ S := by
    have := mul_le_mul_of_nonneg_left htwo hmpos
    nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- Explicit analytic inequalities imply the required exponential denominator window. -/
theorem auxiliaryDenominator_exp_bounds {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) (S L U D : ℝ)
    (hpL : ∀ j, L ≤ Real.log (p j : ℝ))
    (hpU : ∀ j, Real.log (p j : ℝ) ≤ U)
    (hqU : ∀ i j e, Real.log (q i j e : ℝ) ≤ U)
    (hLower : S < (m : ℝ) * L)
    (hUpper : (a : ℝ) * Real.log 2 + (2 * (R : ℝ) + 1) * (m : ℝ) * U ≤ D * S) :
    Real.exp S < (auxiliaryDenominator a p q : ℝ) ∧
      (auxiliaryDenominator a p q : ℝ) ≤ Real.exp (D * S) := by
  have hpos : (0 : ℝ) < auxiliaryDenominator a p q := by
    exact_mod_cast auxiliaryDenominator_pos a p q hp hq
  constructor
  · calc
      Real.exp S < Real.exp (Real.log (auxiliaryDenominator a p q : ℝ)) :=
        Real.exp_lt_exp.mpr (hLower.trans_le (log_auxiliaryDenominator_ge a p q hp hq L hpL))
      _ = (auxiliaryDenominator a p q : ℝ) := Real.exp_log hpos
  · calc
      (auxiliaryDenominator a p q : ℝ) = Real.exp (Real.log (auxiliaryDenominator a p q : ℝ)) :=
        (Real.exp_log hpos).symm
      _ ≤ Real.exp (D * S) := Real.exp_le_exp.mpr
        ((log_auxiliaryDenominator_le a p q hp hq U hpU hqU).trans hUpper)

/-- Constructs the entire denominator-size/divisibility portion of the residue lemma.
Only the prime-scale factor bounds and elementary floor-scale bounds are required here. -/
theorem construct_residue_denominator {m : ℕ} (p : Fin m → ℕ)
    (q : Fin 1000 → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) {S : ℝ}
    (hS : 1 ≤ S) (hlog : 1 ≤ Real.log S) (hlarge : 100 * Real.log S ≤ S)
    (hmLower : S - Real.log S ≤ (m : ℝ) * Real.log S)
    (hmUpper : (m : ℝ) * Real.log S ≤ S)
    (hpL : ∀ j, 100 * Real.log S ≤ Real.log (p j : ℝ))
    (hpU : ∀ j, Real.log (p j : ℝ) ≤ 100 * Real.log S + Real.log 2)
    (hqU : ∀ i j e, Real.log (q i j e : ℝ) ≤ 100 * Real.log S + Real.log 2) :
    ∃ M : ℕ, Real.exp S < (M : ℝ) ∧ (M : ℝ) ≤ Real.exp (204204 * S) ∧
      2 ^ ⌈100000 * Real.log S / Real.log 2⌉₊ ∣ M ∧
      (∀ I : Fin m → Fin 2, subsetEntry p I ∣ M ∧ 1 ≤ subsetEntry p I ∧
        (subsetEntry p I : ℝ) ≤ Real.exp (101 * S)) ∧
      (∀ i (I : Fin m → Fin 2), pairedEntry (q i) I ∣ M ∧ 1 ≤ pairedEntry (q i) I ∧
        (pairedEntry (q i) I : ℝ) ≤ Real.exp (101 * S)) := by
  obtain ⟨a, hcut, ha⟩ := exists_binary_cutoff hS 100000
  norm_num only [Nat.cast_ofNat] at ha
  obtain ⟨hLower, hUpper, hEntry⟩ := residue_size_budget hlog hlarge hmLower hmUpper ha
  obtain ⟨hMl, hMu⟩ := auxiliaryDenominator_exp_bounds a p q hp hq S
    (100 * Real.log S) (100 * Real.log S + Real.log 2) 204204
    hpL hpU hqU hLower (by simpa using hUpper)
  refine ⟨auxiliaryDenominator a p q, hMl, hMu, ?_, ?_, ?_⟩
  · simpa using ceiling_binary_factor_dvd_auxiliary a 100000 p q (by linarith : 0 < S) hcut
  · intro I
    have hpos := subsetEntry_pos p hp I
    refine ⟨subsetEntry_dvd_auxiliary a p q I, hpos, ?_⟩
    calc
      (subsetEntry p I : ℝ) = Real.exp (Real.log (subsetEntry p I : ℝ)) :=
        (Real.exp_log (by exact_mod_cast hpos)).symm
      _ ≤ Real.exp (101 * S) := Real.exp_le_exp.mpr
        ((log_subsetEntry_le p hp I _ (by positivity) hpU).trans hEntry)
  · intro i I
    have hpos := pairedEntry_pos (q i) (hq i) I
    refine ⟨pairedEntry_dvd_auxiliary a p q i I, hpos, ?_⟩
    calc
      (pairedEntry (q i) I : ℝ) = Real.exp (Real.log (pairedEntry (q i) I : ℝ)) :=
        (Real.exp_log (by exact_mod_cast hpos)).symm
      _ ≤ Real.exp (101 * S) := Real.exp_le_exp.mpr
        ((log_pairedEntry_le (q i) (hq i) I _ (hqU i)).trans hEntry)

end Problem337.ResidueConstruction

end

end OAI
