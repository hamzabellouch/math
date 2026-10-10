import Mathlib.NumberTheory.SelbergSieve
import Mathlib

namespace OAI
noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open Finset ArithmeticFunction

namespace Problem337.SelbergOptimal

/-- Complementation turns a sum over multiples among divisors into a divisor sum. -/
theorem sum_multiples_complement (P l : ℕ) (hP : P ≠ 0) (hl : l ∣ P)
    (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then f (P / d) else 0) =
      ∑ d ∈ (P / l).divisors, f d := by
  calc
    _ = ∑ d ∈ P.divisors, if l ∣ P / d then f d else 0 := by
      rw [← Nat.sum_div_divisors P (fun d => if l ∣ d then f (P / d) else 0)]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hP]
    _ = ∑ d ∈ (P / l).divisors, f d := by
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd, _⟩, hld⟩
        refine ⟨?_, Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
          (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl)))⟩
        apply (Nat.dvd_div_iff_mul_dvd hl).2
        rw [Nat.mul_comm]
        exact (Nat.dvd_div_iff_mul_dvd hd).1 hld
      · rintro ⟨hd, _⟩
        have hdP : d ∣ P := hd.trans (Nat.div_dvd_of_dvd hl)
        refine ⟨⟨hdP, hP⟩, ?_⟩
        apply (Nat.dvd_div_iff_mul_dvd hdP).2
        rw [Nat.mul_comm]
        exact (Nat.dvd_div_iff_mul_dvd hl).1 hd

/-- Inverse of the upper divisor-sum transform, expressed through ordinary
Möbius inversion after complementing divisors. -/
def upperInverse (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ x ∈ (P / d).divisorsAntidiagonal, (μ x.1 : ℝ) * y (P / x.2)

theorem sum_upperInverse (P l : ℕ) (hP : P ≠ 0) (hl : l ∣ P)
    (y : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then upperInverse P y d else 0) = y l := by
  let f : ℕ → ℝ := fun n =>
    ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ) * y (P / x.2)
  have hmob : ∀ n > 0, ∑ d ∈ n.divisors, f d = y (P / n) := by
    apply ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr
    intro n hn
    rfl
  change (∑ d ∈ P.divisors, if l ∣ d then f (P / d) else 0) = y l
  rw [sum_multiples_complement P l hP hl f]
  rw [hmob (P / l) (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
    (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl)))]
  rw [Nat.div_div_self hl hP]

theorem upperInverse_one (P : ℕ) (hP : P ≠ 0) (y : ℕ → ℝ) :
    upperInverse P y 1 = ∑ d ∈ P.divisors, (μ d : ℝ) * y d := by
  unfold upperInverse
  rw [Nat.div_one, Nat.sum_divisorsAntidiagonal (f := fun d e => (μ d : ℝ) * y (P / e))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hP]

/-- The positive finite normalizing sum of the optimal Selberg weights. -/
def normalizer (s : BoundingSieve) (z : ℕ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, if d ≤ z then s.selbergTerms d else 0

theorem normalizer_pos (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    0 < normalizer s z := by
  apply Finset.sum_pos'
  · intro d hd
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le
    · exact le_rfl
  · refine ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_ne_zero⟩, ?_⟩
    rw [ite_eq_left hz]
    exact s.selbergTerms_pos (one_dvd _)

/-- The diagonal coordinates attaining the constrained minimum. -/
def optimalDiagonal (s : BoundingSieve) (z d : ℕ) : ℝ :=
  if d ≤ z then (μ d : ℝ) * s.selbergTerms d / normalizer s z else 0

/-- Selberg weights obtained by upper Möbius inversion. -/
def optimalWeight (s : BoundingSieve) (z d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then
    upperInverse s.prodPrimes (optimalDiagonal s z) d / s.nu d else 0

theorem optimalWeight_transform (s : BoundingSieve) (z l : ℕ)
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then s.nu d * optimalWeight s z d else 0) =
      optimalDiagonal s z l := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then upperInverse s.prodPrimes (optimalDiagonal s z) d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors hd
      rw [optimalWeight, ite_eq_left hdP]
      have hnu := s.nu_ne_zero hdP
      congr 1
      field_simp
    _ = _ := sum_upperInverse _ _ s.prodPrimes_ne_zero hl _

theorem optimalWeight_one (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    optimalWeight s z 1 = 1 := by
  rw [optimalWeight, ite_eq_left (one_dvd _), s.nu_mult.map_one, div_one,
    upperInverse_one _ s.prodPrimes_ne_zero]
  have hG : normalizer s z ≠ 0 := (normalizer_pos s hz).ne'
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then s.selbergTerms d else 0) / normalizer s z := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hmu : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      unfold optimalDiagonal
      split_ifs with he
      · rw [mul_div_assoc, ← mul_assoc, ← pow_two, hmu, one_mul]
      · simp
    _ = 1 := div_self hG

/-- The diagonalized main term at the optimal weights is exactly the
reciprocal of the finite Selberg normalizer. -/
theorem mainSum_optimalWeight (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.mainSum (BoundingSieve.lambdaSquared (optimalWeight s z)) =
      1 / normalizer s z := by
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hG : normalizer s z ≠ 0 := (normalizer_pos s hz).ne'
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then s.selbergTerms d else 0) / normalizer s z ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors hd
      have hg : s.selbergTerms d ≠ 0 := (s.selbergTerms_pos hdP).ne'
      have hmu : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      rw [optimalWeight_transform s z d hdP]
      unfold optimalDiagonal
      split_ifs with he
      · rw [div_pow, mul_pow, hmu, one_mul]
        field_simp
      · simp
    _ = 1 / normalizer s z := by
      change normalizer s z / normalizer s z ^ 2 = _
      field_simp

/-- The Selberg upper-bound sieve with its main term optimized. -/
theorem siftedSum_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.siftedSum ≤ s.totalMass / normalizer s z +
      s.errSum (BoundingSieve.lambdaSquared (optimalWeight s z)) := by
  have h := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared (optimalWeight s z))
    (BoundingSieve.upperMoebius_lambdaSquared _ (optimalWeight_one s hz))
  rw [mainSum_optimalWeight s hz, mul_one_div] at h
  exact h

/-- No optimal weight lies above the chosen truncation. -/
theorem optimalWeight_eq_zero_of_lt (s : BoundingSieve) {z d : ℕ} (hzd : z < d) :
    optimalWeight s z d = 0 := by
  unfold optimalWeight
  split_ifs with hdP
  · suffices upperInverse s.prodPrimes (optimalDiagonal s z) d = 0 by rw [this, zero_div]
    unfold upperInverse
    apply Finset.sum_eq_zero
    intro x hx
    have hx2 : x.2 ∣ s.prodPrimes / d :=
      Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
    have hxP : x.2 ∣ s.prodPrimes := hx2.trans (Nat.div_dvd_of_dvd hdP)
    have hdx : d ∣ s.prodPrimes / x.2 := by
      apply (Nat.dvd_div_iff_mul_dvd hxP).2
      rw [Nat.mul_comm]
      exact (Nat.dvd_div_iff_mul_dvd hdP).1 hx2
    have hpos : 0 < s.prodPrimes / x.2 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero s.prodPrimes_ne_zero) hxP)
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hxP))
    have hlong : z < s.prodPrimes / x.2 := hzd.trans_le (Nat.le_of_dvd hpos hdx)
    simp [optimalDiagonal, not_le.mpr hlong]
  · rfl

/-- Upper Möbius inversion does not increase the crude full-divisor
absolute-mass bound. This estimate is independent of squarefreeness. -/
theorem abs_upperInverse_le (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (y : ℕ → ℝ) :
    |upperInverse P y d| ≤ ∑ e ∈ P.divisors, |y e| := by
  unfold upperInverse
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ a : ℝ) * y (P / b))]
  calc
    _ ≤ ∑ e ∈ (P / d).divisors, |(μ ((P / d) / e) : ℝ) * y (P / e)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ (P / d).divisors, |y (P / e)| := by
      apply Finset.sum_le_sum
      intro e he
      have hmu : |(μ ((P / d) / e) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (P / d) / e)
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right hmu (abs_nonneg (y (P / e)))
    _ ≤ ∑ e ∈ P.divisors, |y (P / e)| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        exact Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors he).trans (Nat.div_dvd_of_dvd hd), hP⟩
      · intro e he hnot
        exact abs_nonneg _
    _ = _ := Nat.sum_div_divisors P (fun e => |y e|)

/-- The optimal diagonal coordinates have total absolute mass one. -/
theorem sum_abs_optimalDiagonal (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ s.prodPrimes.divisors, |optimalDiagonal s z d|) = 1 := by
  have hG := normalizer_pos s hz
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then s.selbergTerms d else 0) / normalizer s z := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hg := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)
      have hmu : |(μ d : ℝ)| = 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      unfold optimalDiagonal
      split_ifs
      · rw [abs_div, abs_mul, hmu, abs_of_pos hg, abs_of_pos hG, one_mul]
      · simp
    _ = 1 := div_self hG.ne'

/-- A coefficient bound adequate for polynomial-error applications of the sieve. -/
theorem abs_optimalWeight_le (s : BoundingSieve) {z d : ℕ} (hz : 1 ≤ z)
    (hd : d ∣ s.prodPrimes) :
    |optimalWeight s z d| ≤ (s.nu d)⁻¹ := by
  rw [optimalWeight, ite_eq_left hd, abs_div, abs_of_pos (s.nu_pos_of_dvd_prodPrimes hd)]
  have h := abs_upperInverse_le s.prodPrimes d s.prodPrimes_ne_zero hd
    (optimalDiagonal s z)
  rw [sum_abs_optimalDiagonal s hz] at h
  simpa only [one_div] using div_le_div_of_nonneg_right h
    (s.nu_pos_of_dvd_prodPrimes hd).le

/-- The upper inverse in the more usual sum-over-multiples form. -/
theorem upperInverse_eq_sum_multiples (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (y : ℕ → ℝ) :
    upperInverse P y d =
      ∑ e ∈ P.divisors, if d ∣ e then (μ (e / d) : ℝ) * y e else 0 := by
  unfold upperInverse
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ a : ℝ) * y (P / b)),
    ← sum_multiples_complement P d hP hd
      (fun e => (μ ((P / d) / e) : ℝ) * y (P / e))]
  apply Finset.sum_congr rfl
  intro e he
  have heP := Nat.dvd_of_mem_divisors he
  rw [Nat.div_div_self heP hP]
  split_ifs with hde
  · have hPe : 0 < P / e := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) heP)
      (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP heP))
    have hquot : (P / d) / (P / e) = e / d := by
      rw [← Nat.div_mul_div heP hde, Nat.mul_comm, Nat.mul_div_cancel _ hPe]
    rw [hquot]
  · rfl

/-- Divisor multiples are parametrized by the complementary quotient. -/
theorem sum_multiples_eq (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (f : ℕ → ℝ) :
    (∑ e ∈ P.divisors, if d ∣ e then f e else 0) =
      ∑ t ∈ (P / d).divisors, f (d * t) := by
  calc
    _ = ∑ e ∈ P.divisors, if d ∣ e then f (P / (P / e)) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) hP]
    _ = ∑ t ∈ (P / d).divisors, f (P / t) :=
      sum_multiples_complement P d hP hd (fun t => f (P / t))
    _ = ∑ t ∈ (P / d).divisors, f (d * t) := by
      rw [← Nat.sum_div_divisors (P / d) (fun t => f (P / t))]
      apply Finset.sum_congr rfl
      intro t ht
      have htQ := Nat.dvd_of_mem_divisors ht
      have hQpos : 0 < P / d := Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hd)
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hd))
      have hQt : 0 < (P / d) / t := Nat.div_pos (Nat.le_of_dvd hQpos htQ)
        (Nat.pos_of_mem_divisors ht)
      have hprod : ((P / d) / t) * (d * t) = P := by
        calc
          _ = d * (((P / d) / t) * t) := by ring
          _ = d * (P / d) := by rw [Nat.div_mul_cancel htQ]
          _ = P := Nat.mul_div_cancel' hd
      congr 1
      conv_lhs => arg 1; rw [← hprod]
      exact Nat.mul_div_cancel_left (d * t) hQt

/-- The two Möbius signs from upper inversion collapse on squarefree divisors. -/
theorem moebius_div_mul (e d : ℕ) (he : Squarefree e) (hd : d ∣ e) :
    (μ (e / d) : ℝ) * (μ e : ℝ) = (μ d : ℝ) := by
  have hm : d * (e / d) = e := Nat.mul_div_cancel' hd
  have hcop : d.Coprime (e / d) := Nat.coprime_of_squarefree_mul (hm.symm ▸ he)
  have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  rw [hm] at hmu
  have heq : (μ e : ℝ) = (μ d : ℝ) * (μ (e / d) : ℝ) := by exact_mod_cast hmu
  have hsquare : (μ (e / d) : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
      (he.squarefree_of_dvd (Nat.div_dvd_of_dvd hd))
  rw [heq]
  calc
    _ = (μ d : ℝ) * (μ (e / d) : ℝ) ^ 2 := by ring
    _ = _ := by rw [hsquare, mul_one]

/-- The truncated normalizer on complementary divisors. -/
def complementNormalizer (s : BoundingSieve) (z d : ℕ) : ℝ :=
  ∑ t ∈ (s.prodPrimes / d).divisors, if t ≤ z / d then s.selbergTerms t else 0

/-- Explicit classical formula for the optimal coefficient. In particular,
the sign is the Möbius sign and the remaining factors are nonnegative. -/
theorem optimalWeight_formula (s : BoundingSieve) (z d : ℕ)
    (hd : d ∣ s.prodPrimes) :
    optimalWeight s z d = (μ d : ℝ) * s.selbergTerms d / s.nu d *
      (complementNormalizer s z d / normalizer s z) := by
  rw [optimalWeight, ite_eq_left hd,
    upperInverse_eq_sum_multiples _ _ s.prodPrimes_ne_zero hd]
  have hdpos : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd)
  have hsum :
      (∑ e ∈ s.prodPrimes.divisors,
        if d ∣ e then (μ (e / d) : ℝ) * optimalDiagonal s z e else 0) =
      (μ d : ℝ) / normalizer s z *
        (s.selbergTerms d * complementNormalizer s z d) := by
    calc
      _ = (μ d : ℝ) / normalizer s z *
          (∑ e ∈ s.prodPrimes.divisors,
            if d ∣ e then (if e ≤ z then s.selbergTerms e else 0) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        by_cases hde : d ∣ e
        · rw [ite_eq_left hde, ite_eq_left hde]
          unfold optimalDiagonal
          split_ifs with hez
          · rw [mul_div_assoc, ← mul_assoc,
              moebius_div_mul e d (s.squarefree_of_mem_divisors_prodPrimes he) hde]
            ring
          · simp
        · simp [hde]
      _ = (μ d : ℝ) / normalizer s z *
          (∑ t ∈ (s.prodPrimes / d).divisors,
            if d * t ≤ z then s.selbergTerms (d * t) else 0) := by
        rw [sum_multiples_eq _ _ s.prodPrimes_ne_zero hd]
      _ = _ := by
        congr 1
        unfold complementNormalizer
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have htQ := Nat.dvd_of_mem_divisors ht
        have hdt : d * t ∣ s.prodPrimes := by
          simpa [Nat.mul_comm] using (Nat.dvd_div_iff_mul_dvd hd).1 htQ
        have hcop : d.Coprime t := Nat.coprime_of_squarefree_mul
          (s.squarefree_of_dvd_prodPrimes hdt)
        have hiff : d * t ≤ z ↔ t ≤ z / d := by
          rw [Nat.le_div_iff_mul_le hdpos, Nat.mul_comm]
        simp only [hiff]
        split_ifs
        · exact s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop
        · simp
  rw [hsum]
  ring

end Problem337.SelbergOptimal

end

end OAI
