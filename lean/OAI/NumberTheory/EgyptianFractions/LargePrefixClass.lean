import OAI.NumberTheory.EgyptianFractions.LargePrimeDivisors
import OAI.NumberTheory.EgyptianFractions.DivisorPrefixCounting

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The large-prime class, including integers already below the prefix cutoff.
The existential witnesses need not be chosen canonically. -/
def InLargePrefixClass (Z L : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) ≤ Z ∨ ∃ d p : ℕ, d ∣ n ∧ (d : ℝ) ≤ Z ∧ p.Prime ∧
    L ≤ Real.log (p : ℝ) ∧
    ∀ q : ℕ, q.Prime → q ∣ n / d → p ≤ q

/-- Each member of the large-prime class has a divisor-indexed moment majorant. -/
theorem large_prefix_class_majorant (X W r Z L : ℝ) {n : ℕ}
    (hn : 0 < n) (hX : 1 < X) (hXW : Real.log X ≤ W)
    (hnW : Real.log (n : ℝ) ≤ W) (hr : 0 ≤ r) (hL : 0 < L)
    (hclass : InLargePrefixClass Z L n) :
    ∃ d : ℕ, 0 < d ∧ d ∣ n ∧ (d : ℝ) ≤ Z ∧
      (truncatedDivisorCount X n : ℝ) ^ r ≤ (d.divisors.card : ℝ) ^ r *
        Real.exp (r * ((1 + Real.log (W / Real.log X)) * Real.log X / L)) := by
  have hv : 0 < Real.log X := Real.log_pos hX
  have hW : 0 < W := hv.trans_le hXW
  have hratio : 1 ≤ W / Real.log X := (le_div_iff₀ hv).2 (by simpa using hXW)
  have hB : 0 ≤ 1 + Real.log (W / Real.log X) := by
    have := Real.log_nonneg hratio
    linarith
  have hH : 0 ≤ r * ((1 + Real.log (W / Real.log X)) * Real.log X / L) := by positivity
  rcases hclass with hsmall | ⟨d, p, hd, hdZ, hp, hpL, hrough⟩
  · refine ⟨n, hn, dvd_refl n, hsmall, ?_⟩
    have hcount : truncatedDivisorCount X n ≤ n.divisors.card := by
      exact Finset.card_filter_le _ _
    have hpow : (truncatedDivisorCount X n : ℝ) ^ r ≤ (n.divisors.card : ℝ) ^ r :=
      Real.rpow_le_rpow (Nat.cast_nonneg (truncatedDivisorCount X n))
        (by exact_mod_cast hcount) hr
    apply hpow.trans
    have he : 1 ≤ Real.exp (r * ((1 + Real.log (W / Real.log X)) * Real.log X / L)) :=
      Real.one_le_exp hH
    simpa using mul_le_mul_of_nonneg_left he (Real.rpow_nonneg (Nat.cast_nonneg _) r)
  · have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
    refine ⟨d, hdpos, hd, hdZ, ?_⟩
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hbound := truncatedDivisorCount_prefix_moment_bound X (p : ℝ) W r
      hn.ne' hd hX hpR hXW hnW hr (by
        intro a ha
        exact_mod_cast hrough a (Nat.prime_of_mem_primeFactorsList ha)
          (Nat.dvd_of_mem_primeFactorsList ha))
    apply hbound.trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) r)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hr
    exact div_le_div_of_nonneg_left (by positivity) hL hpL

/-- Actual weighted sum over the large-prime class in a translated real interval. -/
theorem large_prefix_class_moment_bound (X W r Z L Y : ℝ) (N : ℕ) (A : Finset ℕ)
    (hX : 1 < X) (hXW : Real.log X ≤ W) (hr : 0 ≤ r) (hL : 0 < L)
    (hZ : 1 ≤ Z) (hZY : Z ≤ Y)
    (hA : A ⊆ Finset.Ioc N (N + ⌊Y⌋₊))
    (hW : ∀ n ∈ A, Real.log (n : ℝ) ≤ W)
    (hclass : ∀ n ∈ A, InLargePrefixClass Z L n) :
    (∑ n ∈ A, (truncatedDivisorCount X n : ℝ) ^ r) ≤
      2 * Y * Real.exp (r * ((1 + Real.log (W / Real.log X)) * Real.log X / L)) *
        ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, (d.divisors.card : ℝ) ^ r / d := by
  classical
  let H := r * ((1 + Real.log (W / Real.log X)) * Real.log X / L)
  have hY : 0 ≤ Y := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hbound := DivisorMoment.sum_le_divisor_majorant_real_cutoff N Y A
    (Finset.Icc 1 ⌊Z⌋₊) (fun n => (truncatedDivisorCount X n : ℝ) ^ r)
    (fun d => (d.divisors.card : ℝ) ^ r * Real.exp H) hY hA
    (by
      intro n hn
      have hnpos : 0 < n := by have := (Finset.mem_Ioc.mp (hA hn)).1; omega
      obtain ⟨d, hdpos, hd, hdZ, hmajor⟩ :=
        large_prefix_class_majorant X W r Z L hnpos hX hXW (hW n hn) hr hL (hclass n hn)
      exact ⟨d, Finset.mem_Icc.mpr ⟨hdpos, Nat.le_floor hdZ⟩, hd, hmajor⟩)
    (by intro d hd; positivity)
    (by
      intro d hd
      obtain ⟨hdpos, hdZ⟩ := Finset.mem_Icc.mp hd
      exact ⟨hdpos, ((by exact_mod_cast hdZ : (d : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans
        (Nat.floor_le hZ0)).trans hZY⟩)
  calc
    _ ≤ 2 * Y * ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, (d.divisors.card : ℝ) ^ r * Real.exp H / d := hbound
    _ = 2 * Y * ((∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, (d.divisors.card : ℝ) ^ r / d) * Real.exp H) := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by dsimp [H]; ring

/-- The manuscript's large-prime estimate, with threshold `(log X)^(15/16)`. -/
theorem large_prefix_class_sqrt_moment_bound (X W r Y : ℝ) (N : ℕ) (A : Finset ℕ)
    (hX : 1 < X) (hXW : Real.log X ≤ W) (hr : 0 ≤ r) (hY : 1 ≤ Y)
    (hA : A ⊆ Finset.Ioc N (N + ⌊Y⌋₊))
    (hW : ∀ n ∈ A, Real.log (n : ℝ) ≤ W)
    (hclass : ∀ n ∈ A, InLargePrefixClass (Real.sqrt Y) ((Real.log X) ^ (15 / 16 : ℝ)) n) :
    (∑ n ∈ A, (truncatedDivisorCount X n : ℝ) ^ r) ≤
      2 * Y * Real.exp (r * (1 + Real.log (W / Real.log X)) * (Real.log X) ^ (1 / 16 : ℝ)) *
        ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt Y⌋₊, (d.divisors.card : ℝ) ^ r / d := by
  have hv : 0 < Real.log X := Real.log_pos hX
  have hZ : 1 ≤ Real.sqrt Y := (Real.le_sqrt (by norm_num) (by linarith)).2 (by nlinarith)
  have hZY : Real.sqrt Y ≤ Y := by
    apply (Real.sqrt_le_iff).2
    constructor <;> nlinarith
  have hpow : Real.log X / (Real.log X) ^ (15 / 16 : ℝ) =
      (Real.log X) ^ (1 / 16 : ℝ) := by
    calc
      _ = (Real.log X) ^ (1 : ℝ) / (Real.log X) ^ (15 / 16 : ℝ) := by rw [Real.rpow_one]
      _ = (Real.log X) ^ ((1 : ℝ) - 15 / 16) := (Real.rpow_sub hv _ _).symm
      _ = _ := by norm_num
  have hb := large_prefix_class_moment_bound X W r (Real.sqrt Y)
    ((Real.log X) ^ (15 / 16 : ℝ)) Y N A hX hXW hr (by positivity) hZ hZY hA hW hclass
  convert hb using 1
  congr 3
  rw [mul_div_assoc, hpow]
  ring

/-- Shifted-index version, matching the uniform short-interval moment statement. -/
theorem large_prefix_class_shifted_sqrt_moment_bound (X W r Y : ℝ) (N : ℕ) (A : Finset ℕ)
    (hX : 1 < X) (hXW : Real.log X ≤ W) (hr : 0 ≤ r) (hY : 1 ≤ Y)
    (hA : A ⊆ Finset.Icc 1 ⌊Y⌋₊)
    (hW : ∀ h ∈ A, Real.log ((N + h : ℕ) : ℝ) ≤ W)
    (hclass : ∀ h ∈ A, InLargePrefixClass (Real.sqrt Y)
      ((Real.log X) ^ (15 / 16 : ℝ)) (N + h)) :
    (∑ h ∈ A, (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
      2 * Y * Real.exp (r * (1 + Real.log (W / Real.log X)) * (Real.log X) ^ (1 / 16 : ℝ)) *
        ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt Y⌋₊, (d.divisors.card : ℝ) ^ r / d := by
  classical
  have hb := large_prefix_class_sqrt_moment_bound X W r Y N
    (A.image (fun h => N + h)) hX hXW hr hY
    (by
      intro n hn
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hhlo, hhhi⟩ := Finset.mem_Icc.mp (hA hh)
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
    (by
      intro n hn
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
      exact hW h hh)
    (by
      intro n hn
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
      exact hclass h hh)
  rw [Finset.sum_image] at hb
  · exact hb
  · intro a ha b hb hab
    exact Nat.add_left_cancel hab

end Problem337

end

end OAI
