import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeLoss
import OAI.NumberTheory.Catalan.Arithmetic.OddPrimePairedColumnIntegrality
import OAI.NumberTheory.Catalan.Determinants.OddPhysicalMinorCounts
import OAI.NumberTheory.Catalan.Polynomial.RationalProductFormula

namespace OAI


namespace InternalCatalan

theorem parityBoundarySum_prime_log_lower {p : ℕ} [Fact p.Prime]
    (f : ℕ → ℚ) (u H : ℕ) (hu : u ≤ H) (B : ℤ) (hB : B ≤ 0)
    (hf : ∀ z, 0 < z → z ≤ H → B ≤ padicValRat p (f z)) :
    B ≤ padicValRat p (parityBoundarySum f u) := by
  unfold parityBoundarySum
  apply prime_sum_valuation_lower _ _ B hB
  intro z hz
  split_ifs with he
  · exact hf z he.1 (by have := Finset.mem_range.mp hz; omega)
  · simpa using hB

theorem boundaryPlus_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (d H : ℕ) (hd : d ≤ H) :
    -5 * (Nat.log p H : ℤ) ≤ padicValRat p (boundaryPlus d) := by
  have hlog : 0 ≤ (Nat.log p H : ℤ) := by positivity
  cases d with
  | zero => simp
  | succ u =>
    rw [boundaryPlus_explicit]
    have hu : u ≤ H := by omega
    have hsum := parityBoundarySum_prime_log_lower boundaryPlusWeight u H hu
      (-3 * (Nat.log p H : ℤ)) (by omega)
      (fun z hz0 hz => boundaryPlusWeight_odd_prime_log_lower hp2 z H hz0 hz)
    have hm := prime_mul_valuation_lower (boundaryFactor u)
      (parityBoundarySum boundaryPlusWeight u)
      (-2 * (Nat.log p H : ℤ)) (-3 * (Nat.log p H : ℤ)) (by omega)
      (boundaryFactor_odd_prime_log_bounds hp2 u H hu).1 hsum
    convert hm using 1
    ring

theorem boundaryMinus_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (d H : ℕ) (hd : d ≤ H) :
    -6 * (Nat.log p H : ℤ) ≤ padicValRat p (boundaryMinus d) := by
  have hlog : 0 ≤ (Nat.log p H : ℤ) := by positivity
  rw [boundaryMinus_explicit]
  have hsum := parityBoundarySum_prime_log_lower boundaryMinusWeight d H hd
    (-4 * (Nat.log p H : ℤ)) (by omega)
    (fun z hz0 hz => boundaryMinusWeight_odd_prime_log_lower hp2 z H hz0 hz)
  have hm := prime_mul_valuation_lower (boundaryFactor d)
    (parityBoundarySum boundaryMinusWeight d)
    (-2 * (Nat.log p H : ℤ)) (-4 * (Nat.log p H : ℤ)) (by omega)
    (boundaryFactor_odd_prime_log_bounds hp2 d H hd).1 hsum
  convert hm using 1
  ring

theorem momentRat_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (i j H : ℕ) (hi : i < H) (hj : j < H) :
    -6 * (Nat.log p H : ℤ) ≤ padicValRat p (momentRat i j) := by
  have hlog : 0 ≤ (Nat.log p H : ℤ) := by positivity
  by_cases hji : j ≤ i
  · rw [momentRat_of_le hji]
    apply prime_sub_valuation_lower _ _ _ (by omega)
    · exact boundaryMinus_odd_prime_log_lower hp2 (i - j) H (by omega)
    · apply prime_sum_valuation_lower _ _ _ (by omega)
      intro k hk
      have hk' : k < j := Finset.mem_range.mp hk
      have hm := prime_div_nat_valuation_lower (p := p)
        (momentScalar (i - j + k)) (k + 1) H (-2 * (Nat.log p H : ℤ))
        (by omega) (by omega) (momentScalar_odd_prime_log_lower hp2 _ H (by omega))
      omega
  · rw [momentRat_of_lt (by omega : i < j)]
    apply prime_sub_valuation_lower _ _ _ (by omega)
    · have hm := boundaryPlus_odd_prime_log_lower (p := p) hp2 (j - i) H (by omega)
      omega
    · apply prime_sum_valuation_lower _ _ _ (by omega)
      intro k hk
      have hk' : k < i := Finset.mem_range.mp hk
      have hm := prime_div_nat_valuation_lower (p := p)
        (momentScalar k) (j - i + k + 1) H (-2 * (Nat.log p H : ℤ))
        (by omega) (by omega) (momentScalar_odd_prime_log_lower hp2 k H (by omega))
      omega





open scoped BigOperators

theorem int_prime_valuation_nonneg (p : ℕ) (m : ℤ) :
    0 ≤ padicValRat p (m : ℚ) := by
  rw [padicValRat.of_int]
  unfold padicValInt
  positivity

theorem rational_prime_valuation_den_lower (p : ℕ) (z : ℚ) :
    -(padicValNat p z.den : ℤ) ≤ padicValRat p z := by
  rw [padicValRat_def]
  have : 0 ≤ (padicValInt p z.num : ℤ) := by unfold padicValInt; positivity
  omega

theorem centralCoeffKernel_odd_prime_nonneg {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (d : ℤ) : 0 ≤ padicValRat p (centralCoeffKernel d) := by
  unfold centralCoeffKernel
  split_ifs
  · exact centralCoeff_odd_prime_nonneg p _ hp.out hp2
  · simp

private theorem prime_add_lower {p : ℕ} [Fact p.Prime] (a b : ℚ) (B : ℤ)
    (hB : B ≤ 0) (ha : B ≤ padicValRat p a) (hb : B ≤ padicValRat p b) :
    B ≤ padicValRat p (a + b) := by
  simpa using prime_sub_valuation_lower a (-b) B hB ha (by simpa using hb)

theorem rawEntryRat_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (N r j : ℕ) (hj : j < H N) :
    -6 * (Nat.log p (H N) : ℤ) - (padicValNat p z.den : ℤ) ≤
      padicValRat p (rawEntryRat z N r j) := by
  let B : ℤ := -6 * (Nat.log p (H N) : ℤ) - (padicValNat p z.den : ℤ)
  have hl : 0 ≤ (Nat.log p (H N) : ℤ) := by positivity
  have hd : 0 ≤ (padicValNat p z.den : ℤ) := by positivity
  have hB : B ≤ 0 := by dsimp [B]; omega
  have hfour : padicValRat p (4 : ℚ) = 0 := by
    rw [show (4 : ℚ) = (2 : ℚ) ^ 2 by norm_num, padicValRat.pow,
      two_odd_prime_valuation hp2]
    norm_num
  have hfourz : -(padicValNat p z.den : ℤ) ≤ padicValRat p (4 * z) := by
    simpa using prime_mul_valuation_lower (4 : ℚ) z 0
      (-(padicValNat p z.den : ℤ)) (by omega) (by rw [hfour])
      (rational_prime_valuation_den_lower p z)
  have h32 : 0 ≤ padicValRat p (3 / 2 : ℚ) := by
    rw [padicValRat.div (by norm_num) (by norm_num), two_odd_prime_valuation hp2]
    simpa using int_prime_valuation_nonneg p 3
  unfold rawEntryRat
  apply prime_sub_valuation_lower _ _ B hB
  · apply prime_sum_valuation_lower _ _ B hB
    intro i hi
    have hi' : i < H N := Finset.mem_range.mp hi
    have hm := momentRat_odd_prime_log_lower hp2 i j (H N) hi' hj
    have he := prime_mul_valuation_lower (4 * z)
      (centralCoeffKernel ((i : ℤ) - j)) (-(padicValNat p z.den : ℤ)) 0
      (by omega) hfourz (centralCoeffKernel_odd_prime_nonneg hp2 _)
    have hs : B ≤ padicValRat p
        (momentRat i j + 4 * z * centralCoeffKernel ((i : ℤ) - j)) :=
      prime_add_lower _ _ B hB (by dsimp [B]; omega) (by dsimp [B]; omega)
    simpa using prime_mul_valuation_lower ((rowP N r).coeff i : ℚ) _ 0 B
      (by simpa using hB) (int_prime_valuation_nonneg p _) hs
  · have hs : B ≤ padicValRat p
        (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j) := by
      apply prime_sum_valuation_lower _ _ B hB
      intro i hi
      have hz := zetaRat_prime_log_lower (p := p) (H N) i j (Finset.mem_range.mp hi) hj
      have hzB : B ≤ padicValRat p (zetaRat i j) := by dsimp [B]; omega
      simpa using prime_mul_valuation_lower ((rowD N r).coeff i : ℚ) _ 0 B
        (by simpa using hB) (int_prime_valuation_nonneg p _) hzB
    simpa using prime_mul_valuation_lower (3 / 2 : ℚ) _ 0 B
      (by simpa using hB) h32 hs

theorem filteredEntryRat_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (N r k : ℕ) (hk : k < n N) :
    -6 * (Nat.log p (H N) : ℤ) - (padicValNat p z.den : ℤ) ≤
      padicValRat p (filteredEntryRat z N r k) := by
  let B : ℤ := -6 * (Nat.log p (H N) : ℤ) - (padicValNat p z.den : ℤ)
  have hB : B ≤ 0 := by
    have : 0 ≤ (Nat.log p (H N) : ℤ) := by positivity
    have : 0 ≤ (padicValNat p z.den : ℤ) := by positivity
    dsimp [B]
    omega
  unfold filteredEntryRat
  apply prime_sum_valuation_lower _ _ B hB
  intro v hv
  have hv' : v ≤ q N := by have := Finset.mem_range.mp hv; omega
  have hj : b N + k + v < H N := by
    have h := rawColumn_lt_L hk hv'
    unfold L H at *
    omega
  have hfilter : 0 ≤ padicValRat p (filterCoeffRat N v) := by
    simpa [filterCoeffRat] using
      int_prime_valuation_nonneg p ((-1 : ℤ) ^ v * ((q N).choose v : ℤ))
  simpa using prime_mul_valuation_lower (filterCoeffRat N v) _ 0 B
    (by simpa using hB) hfilter (rawEntryRat_odd_prime_log_lower hp2 z N r _ hj)

end InternalCatalan



namespace InternalCatalan

open scoped BigOperators

theorem prime_prod_valuation_lower {p : ℕ} [Fact p.Prime] {α : Type*}
    (s : Finset α) (f : α → ℚ) (B : ℤ) (hB : B ≤ 0)
    (hf : ∀ x ∈ s, B ≤ padicValRat p (f x)) :
    (s.card : ℤ) * B ≤ padicValRat p (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcard : (s.card : ℤ) * B ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hB
    have hm := prime_mul_valuation_lower (f a) (∏ x ∈ s, f x) B
      ((s.card : ℤ) * B) (by omega) (hf a (Finset.mem_insert_self a s))
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))
    convert hm using 1
    simp [Finset.card_insert_of_notMem ha, add_mul]
    ring

theorem prime_det_valuation_lower {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (B : ℤ) (hB : B ≤ 0)
    (hM : ∀ i j, B ≤ padicValRat p (M i j)) :
    (Fintype.card ι : ℤ) * B ≤ padicValRat p (Matrix.det M) := by
  classical
  have hcard : (Fintype.card ι : ℤ) * B ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hB
  rw [Matrix.det_apply']
  apply prime_sum_valuation_lower _ _ _ hcard
  intro σ hσ
  have hprod : (Fintype.card ι : ℤ) * B ≤ padicValRat p (∏ j, M (σ j) j) := by
    simpa using prime_prod_valuation_lower Finset.univ (fun j => M (σ j) j)
      B hB (fun j hj => hM (σ j) j)
  simpa using prime_mul_valuation_lower ((Equiv.Perm.sign σ : ℤ) : ℚ)
    (∏ j, M (σ j) j) 0 ((Fintype.card ι : ℤ) * B) (by simpa using hcard)
    (int_prime_valuation_nonneg p _) hprod

theorem determinantRat_odd_prime_log_lower {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (N : ℕ) :
    (n N : ℤ) * (-6 * (Nat.log p (H N) : ℤ) - (padicValNat p z.den : ℤ)) ≤
      padicValRat p (determinantRat z N) := by
  have hB : -6 * (Nat.log p (H N) : ℤ) - (padicValNat p z.den : ℤ) ≤ 0 := by
    have : 0 ≤ (Nat.log p (H N) : ℤ) := by positivity
    have : 0 ≤ (padicValNat p z.den : ℤ) := by positivity
    omega
  simpa only [determinantRat, Fintype.card_fin] using
    prime_det_valuation_lower (fun r k : Fin (n N) => filteredEntryRat z N r.val k.val)
      _ hB (fun r k => filteredEntryRat_odd_prime_log_lower hp2 z N r.val k.val k.isLt)

end InternalCatalan



namespace InternalCatalan

theorem nat_log_mul_log_prime_le {p H : ℕ} (hp : p.Prime) (hH : 0 < H) :
    (Nat.log p H : ℝ) * Real.log p ≤ Real.log H := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpow : (p : ℝ) ^ Nat.log p H ≤ (H : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self p (Nat.ne_of_gt hH)
  have h := Real.log_le_log (pow_pos hpR _) hpow
  simpa only [Real.log_pow] using h

theorem nat_valuation_mul_log_prime_le {p H : ℕ} (hp : p.Prime) (hH : 0 < H) :
    (padicValNat p H : ℝ) * Real.log p ≤ Real.log H := by
  have : Fact p.Prime := ⟨hp⟩
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  calc
    _ ≤ (Nat.log p H : ℝ) * Real.log p :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast padicValNat_le_nat_log (p := p) H)
        (Real.log_nonneg hpR)
    _ ≤ Real.log H := nat_log_mul_log_prime_le hp hH

theorem determinantRat_odd_prime_log_weighted_lower {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) {N : ℕ} (hN : 0 < N) :
    -(n N : ℝ) * (6 * Real.log (H N) + Real.log z.den) ≤
      (padicValRat p (determinantRat z N) : ℝ) * Real.log p := by
  have hH : 0 < H N := by unfold H; omega
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp.out.one_lt.le
  have hlogp := Real.log_nonneg hpR
  have hn : 0 ≤ (n N : ℝ) := by positivity
  have hnat := nat_log_mul_log_prime_le hp.out hH
  have hden := nat_valuation_mul_log_prime_le hp.out z.pos
  have hv : (n N : ℝ) *
      (-6 * (Nat.log p (H N) : ℝ) - (padicValNat p z.den : ℝ)) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
    have hcast : (((n N : ℤ) * (-6 * (Nat.log p (H N) : ℤ) -
        (padicValNat p z.den : ℤ)) : ℤ) : ℝ) ≤
        (padicValRat p (determinantRat z N) : ℝ) :=
      Int.cast_le.mpr (determinantRat_odd_prime_log_lower hp2 z N)
    norm_num only [Int.cast_mul, Int.cast_sub, Int.cast_neg, Int.cast_ofNat,
      Int.cast_natCast] at hcast
    exact hcast
  have hscaled := mul_le_mul_of_nonneg_right hv hlogp
  have herr : (n N : ℝ) *
      (6 * ((Nat.log p (H N) : ℝ) * Real.log p) +
        (padicValNat p z.den : ℝ) * Real.log p) ≤
      (n N : ℝ) * (6 * Real.log (H N) + Real.log z.den) :=
    mul_le_mul_of_nonneg_left (by linarith) hn
  nlinarith

theorem determinantRat_odd_prime_above_degrees_integral {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (z : ℚ) (N : ℕ) (hH : H N < p) (hz : z.den < p) :
    0 ≤ padicValRat p (determinantRat z N) := by
  have hlog : Nat.log p (H N) = 0 := Nat.log_eq_zero_iff.mpr (Or.inl hH)
  have hdiv : ¬p ∣ z.den := Nat.not_dvd_of_pos_of_lt z.pos hz
  have hden : padicValNat p z.den = 0 := padicValNat.eq_zero_of_not_dvd hdiv
  simpa [hlog, hden] using determinantRat_odd_prime_log_lower hp2 z N

end InternalCatalan



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem log_abs_determinantRat_truncated_lower (z : ℚ) {N : ℕ}
    (hN : 0 < N) (hz : z.den ≤ H N) (hdet : determinantRat z N ≠ 0) :
    (padicValRat 2 (determinantRat z N) : ℝ) * Real.log 2 +
      (∑ p ∈ (Finset.Ioc 0 (H N)).filter (fun p => p.Prime ∧ p ≠ 2),
        (padicValRat p (determinantRat z N) : ℝ) * Real.log p) ≤
      Real.log |(determinantRat z N : ℝ)| := by
  classical
  have hH : 0 < H N := Nat.mul_pos (by decide) hN
  let s := (Finset.Ioc 0 (H N)).filter (fun p => p.Prime ∧ p ≠ 2)
  let t := insert 2 s
  let u := rationalPrimeSupport (determinantRat z N) ∪ t
  have htprime : ∀ p ∈ t, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · simpa [h] using Nat.prime_two
    · exact (Finset.mem_filter.mp h).2.1
  have huprime : ∀ p ∈ u, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact prime_of_mem_rationalPrimeSupport _ h
    · exact htprime p h
  have hformula := log_abs_rational_eq_sum_valuations_on (determinantRat z N)
    hdet u Finset.subset_union_left huprime
  have hsum : (∑ p ∈ t, (padicValRat p (determinantRat z N) : ℝ) * Real.log p) ≤
      ∑ p ∈ u, (padicValRat p (determinantRat z N) : ℝ) * Real.log p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    intro p hpu hpt
    have hp := huprime p hpu
    have hp2 : p ≠ 2 := by
      intro h
      apply hpt
      simp [t, h]
    have hpH : H N < p := by
      by_contra h
      apply hpt
      exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hp.pos, by omega⟩, hp, hp2⟩)
    have : Fact p.Prime := ⟨hp⟩
    have hv := determinantRat_odd_prime_above_degrees_integral hp2 z N hpH
      (lt_of_le_of_lt hz hpH)
    exact mul_nonneg (by exact_mod_cast hv)
      (Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (hH.trans hpH)))
  have htwo : 2 ∉ s := by simp [s]
  rw [← hformula] at hsum
  simpa only [t, Finset.sum_insert htwo, s, Nat.cast_ofNat] using hsum

end InternalCatalan

end



namespace InternalCatalan

theorem prime_ne_H {p N : ℕ} (hp : p.Prime) (hN : 0 < N) : p ≠ H N := by
  intro heq
  have hp65 : 65 ≤ p := by
    rw [heq]
    simpa [H] using Nat.mul_le_mul_left 65 (Nat.succ_le_of_lt hN)
  have hdiv : 5 ∣ p := by
    rw [heq]
    exact ⟨13 * N, by unfold H; omega⟩
  have hfive := hp.eq_one_or_self_of_dvd 5 hdiv
  omega

theorem determinantRat_above_degrees_local_integral {p N : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hH : H N ≤ p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    0 ≤ padicValRat p (determinantRat z N) := by
  have hlt : H N < p := lt_of_le_of_ne hH (Ne.symm (prime_ne_H hp.out hN))
  have hlog : Nat.log p (H N) = 0 := Nat.log_eq_zero_iff.mpr (Or.inl hlt)
  have hdiv : ¬ p ∣ z.den := fun hd => hz ((ZMod.natCast_eq_zero_iff z.den p).mpr hd)
  have hden : padicValNat p z.den = 0 := padicValNat.eq_zero_of_not_dvd hdiv
  simpa [hlog, hden] using determinantRat_odd_prime_log_lower hp2 z N

theorem determinantRat_odd_prime_loss_above_degrees {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 0 < N) (hH : H N ≤ p)
    (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(N : ℝ) * oddPrimeLoss ((p : ℝ) / N) ≤
      (padicValRat p (determinantRat z N) : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hHR : (65 : ℝ) * N ≤ p := by exact_mod_cast hH
  have hratio : (65 : ℝ) ≤ (p : ℝ) / N := (le_div_iff₀ hNR).mpr hHR
  rw [oddPrimeLoss_of_ge_65 _ hratio, mul_zero]
  exact_mod_cast determinantRat_above_degrees_local_integral hp2 hN hH z hz

end InternalCatalan



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def smallOddPrimes (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊2 * Real.sqrt (H N)⌋₊).filter (fun p => p.Prime ∧ p ≠ 2)

theorem mem_smallOddPrimes_iff (N p : ℕ) :
    p ∈ smallOddPrimes N ↔ p.Prime ∧ p ≠ 2 ∧ (p : ℝ) ≤ 2 * Real.sqrt (H N) := by
  have hcut : 0 ≤ 2 * Real.sqrt (H N) := by positivity
  simp only [smallOddPrimes, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_, hp⟩, hprime, hp2⟩
    exact ⟨hprime, hp2, (Nat.le_floor_iff hcut).mp hp⟩
  · rintro ⟨hprime, hp2, hp⟩
    exact ⟨⟨hprime.pos, (Nat.le_floor_iff hcut).mpr hp⟩, hprime, hp2⟩

theorem smallOddPrimes_card_le (N : ℕ) :
    ((smallOddPrimes N).card : ℝ) ≤ 2 * Real.sqrt (H N) := by
  have hcard : (smallOddPrimes N).card ≤ ⌊2 * Real.sqrt (H N)⌋₊ := by
    calc
      _ ≤ (Finset.Ioc 0 ⌊2 * Real.sqrt (H N)⌋₊).card := by
        unfold smallOddPrimes
        exact Finset.card_filter_le _ _
      _ = _ := by simp
  have hcast : ((smallOddPrimes N).card : ℝ) ≤ (⌊2 * Real.sqrt (H N)⌋₊ : ℝ) := by
    exact_mod_cast hcard
  exact hcast.trans (Nat.floor_le (by positivity))

def smallOddPrimeContribution (z : ℚ) (N : ℕ) : ℝ :=
  ∑ p ∈ smallOddPrimes N,
    (padicValRat p (determinantRat z N) : ℝ) * Real.log p

def smallOddPrimeError (z : ℚ) (N : ℕ) : ℝ :=
  2 * Real.sqrt (H N) * (n N : ℝ) *
    (6 * Real.log (H N) + Real.log z.den)

theorem smallOddPrimeError_nonneg (z : ℚ) {N : ℕ} (hN : 0 < N) :
    0 ≤ smallOddPrimeError z N := by
  have hH : (1 : ℝ) ≤ (H N : ℝ) := by
    exact_mod_cast (show 1 ≤ H N by unfold H; omega)
  have hden : (1 : ℝ) ≤ (z.den : ℝ) := by
    exact_mod_cast (show 1 ≤ z.den from z.pos)
  have hlogH := Real.log_nonneg hH
  have hlogden := Real.log_nonneg hden
  unfold smallOddPrimeError
  positivity

theorem smallOddPrimeContribution_lower (z : ℚ) {N : ℕ} (hN : 0 < N) :
    -smallOddPrimeError z N ≤ smallOddPrimeContribution z N := by
  let C : ℝ := (n N : ℝ) * (6 * Real.log (H N) + Real.log z.den)
  have hH : (1 : ℝ) ≤ (H N : ℝ) := by
    exact_mod_cast (show 1 ≤ H N by unfold H; omega)
  have hden : (1 : ℝ) ≤ (z.den : ℝ) := by
    exact_mod_cast (show 1 ≤ z.den from z.pos)
  have hlogH := Real.log_nonneg hH
  have hlogden := Real.log_nonneg hden
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : -(((smallOddPrimes N).card : ℝ) * C) ≤ smallOddPrimeContribution z N := by
    calc
      _ = ∑ p ∈ smallOddPrimes N, -C := by simp [nsmul_eq_mul]
      _ ≤ _ := by
        unfold smallOddPrimeContribution
        apply Finset.sum_le_sum
        intro p hp
        rcases (mem_smallOddPrimes_iff N p).mp hp with ⟨hprime, hp2, _⟩
        have : Fact p.Prime := ⟨hprime⟩
        simpa only [C, neg_mul] using determinantRat_odd_prime_log_weighted_lower hp2 z hN
  calc
    -smallOddPrimeError z N = -(2 * Real.sqrt (H N) * C) := by
      dsimp [smallOddPrimeError, C]
      ring
    _ ≤ -(((smallOddPrimes N).card : ℝ) * C) :=
      neg_le_neg (mul_le_mul_of_nonneg_right (smallOddPrimes_card_le N) hC)
    _ ≤ _ := hsum

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Classical
open scoped BigOperators

theorem prime_prod_valuation_weighted_lower {p : ℕ} [Fact p.Prime]
    {α : Type*} (s : Finset α) (f : α → ℚ) (w : α → ℕ)
    (hf : ∀ x ∈ s, -(w x : ℤ) ≤ padicValRat p (f x)) :
    -((∑ x ∈ s, w x : ℕ) : ℤ) ≤ padicValRat p (∏ x ∈ s, f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h := prime_mul_valuation_lower (f a) (∏ x ∈ s, f x)
      (-(w a : ℤ)) (-((∑ x ∈ s, w x : ℕ) : ℤ)) (by omega)
      (hf a (Finset.mem_insert_self a s))
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))
    simpa only [Nat.cast_add, neg_add] using h

theorem oddPhysicalScalar_valuation_lower {p R B C e : ℕ} [hp : Fact p.Prime]
    (a : Fin C → Fin e → ℚ)
    (ha : ∀ j l, ((a j l).den : ZMod p) ≠ 0)
    (j : oddPhysicalIndex R B C) (u : oddPhysicalChoice e j) :
    -(oddPhysicalLoss j u : ℤ) ≤ padicValRat p (oddPhysicalScalar p a j u) := by
  rcases j with j | (j | j)
  · simp [oddPhysicalScalar, oddPhysicalLoss, oddPhysicalIsRetained,
      oddPhysicalIsPaired, oddPhysicalExceptionalTag,
      padicValRat.inv, padicValRat.pow, padicValRat.self hp.out.one_lt]
  · simp [oddPhysicalScalar, oddPhysicalLoss, oddPhysicalIsRetained,
      oddPhysicalIsPaired, oddPhysicalExceptionalTag,
      padicValRat.inv, padicValRat.self hp.out.one_lt]
  · cases u with
    | none => simp [oddPhysicalScalar, oddPhysicalLoss, oddPhysicalIsRetained,
        oddPhysicalIsPaired, oddPhysicalExceptionalTag]
    | some l =>
      have h := prime_mul_valuation_lower (p : ℚ)⁻¹ (a j l) (-1) 0 (by omega)
        (by simp [padicValRat.inv, padicValRat.self hp.out.one_lt])
        (rational_valuation_nonneg_of_den_ne_zero (ha j l))
      simpa [oddPhysicalScalar, oddPhysicalLoss, oddPhysicalIsRetained,
        oddPhysicalIsPaired, oddPhysicalExceptionalTag] using h

theorem oddPhysicalVector_valuation_nonneg {p n R B C e : ℕ} [Fact p.Prime]
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (hU : ∀ j r, ((U j r).den : ZMod p) ≠ 0)
    (hW : ∀ j r, ((W j r).den : ZMod p) ≠ 0)
    (hI : ∀ j r, ((I j r).den : ZMod p) ≠ 0)
    (hV : ∀ j r, ((V j r).den : ZMod p) ≠ 0)
    (j : oddPhysicalIndex R B C) (u : oddPhysicalChoice e j) (r : Fin n) :
    0 ≤ padicValRat p (oddPhysicalVector U W I V j u r) := by
  apply rational_valuation_nonneg_of_den_ne_zero
  rcases j with j | (j | j)
  · exact hU j r
  · exact hW j r
  · cases u with
    | none => exact hI j r
    | some l => exact hV l r

theorem oddPhysicalVectorMinor_valuation_nonneg {p n R B C e : ℕ} [Fact p.Prime]
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (hU : ∀ j r, ((U j r).den : ZMod p) ≠ 0)
    (hW : ∀ j r, ((W j r).den : ZMod p) ≠ 0)
    (hI : ∀ j r, ((I j r).den : ZMod p) ≠ 0)
    (hV : ∀ j r, ((V j r).den : ZMod p) ≠ 0)
    (c : Fin n → oddPhysicalIndex R B C)
    (u : ∀ k, oddPhysicalChoice e (c k)) :
    0 ≤ padicValRat p (oddPhysicalVectorMinor U W I V c u) := by
  simpa only [mul_zero, oddPhysicalVectorMinor] using prime_det_valuation_lower
    (Matrix.of fun r k => oddPhysicalVector U W I V (c k) (u k) r)
    0 (by omega)
    (fun r k => oddPhysicalVector_valuation_nonneg U W I V hU hW hI hV (c k) (u k) r)

theorem oddPhysicalMinor_valuation_lower {p n R B C e : ℕ} [Fact p.Prime]
    (U : Fin R → Fin n → ℚ) (W : Fin B → Fin n → ℚ)
    (I : Fin C → Fin n → ℚ) (V : Fin e → Fin n → ℚ)
    (a : Fin C → Fin e → ℚ)
    (hU : ∀ j r, ((U j r).den : ZMod p) ≠ 0)
    (hW : ∀ j r, ((W j r).den : ZMod p) ≠ 0)
    (hI : ∀ j r, ((I j r).den : ZMod p) ≠ 0)
    (hV : ∀ j r, ((V j r).den : ZMod p) ≠ 0)
    (ha : ∀ j l, ((a j l).den : ZMod p) ≠ 0)
    (c : Fin n → oddPhysicalIndex R B C) (hc : Function.Injective c) :
    -((min (2 * n) (min (n + R) (2 * R + B + e)) : ℕ) : ℤ) ≤
      padicValRat p (Matrix.det (Matrix.of fun r k =>
        oddPhysicalColumn p U W I V a (c k) r)) := by
  rw [oddPhysicalMinor_expansion]
  apply prime_sum_valuation_lower _ _ _ (by omega)
  intro u hu
  by_cases hdet : oddPhysicalVectorMinor U W I V c u = 0
  · rw [hdet, mul_zero, padicValRat.zero]
    omega
  have hcount := oddPhysical_total_loss_le_min U W I V c hc u hdet
  have hscal := prime_prod_valuation_weighted_lower Finset.univ
    (fun k => oddPhysicalScalar p a (c k) (u k))
    (fun k => oddPhysicalLoss (c k) (u k))
    (fun k _ => oddPhysicalScalar_valuation_lower a ha (c k) (u k))
  have hvect := oddPhysicalVectorMinor_valuation_nonneg U W I V hU hW hI hV c u
  have hterm := prime_mul_valuation_lower
    (∏ k, oddPhysicalScalar p a (c k) (u k)) (oddPhysicalVectorMinor U W I V c u)
    (-((∑ k, oddPhysicalLoss (c k) (u k) : ℕ) : ℤ)) 0 (by omega) hscal hvect
  have hcint : ((∑ k, oddPhysicalLoss (c k) (u k) : ℕ) : ℤ) ≤
      ((min (2 * n) (min (n + R) (2 * R + B + e)) : ℕ) : ℤ) := by exact_mod_cast hcount
  omega

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Filter
open scoped Topology

theorem log_nat_div_sqrt_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h := (hl.comp hs).const_mul 2
  simp only [mul_zero] at h
  apply h.congr
  intro N
  dsimp only [Function.comp_def]
  rw [Real.log_sqrt (Nat.cast_nonneg N)]
  ring

theorem smallOddPrimeError_div_sq_eq (z : ℚ) {N : ℕ} (hN : 0 < N) :
    smallOddPrimeError z N / (n N : ℝ) ^ 2 =
      (2 * Real.sqrt 65 / 48) *
        ((6 * Real.log 65 + Real.log z.den) * (Real.sqrt (N : ℝ))⁻¹ +
          6 * (Real.log (N : ℝ) / Real.sqrt (N : ℝ))) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold smallOddPrimeError
  simp only [H, n, Nat.cast_mul, Nat.cast_ofNat,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 65)]
  rw [Real.log_mul (by norm_num : (65 : ℝ) ≠ 0) hNr]
  calc
    _ = (2 * Real.sqrt 65 / 48) * (Real.sqrt (N : ℝ) / (N : ℝ)) *
        (6 * (Real.log 65 + Real.log (N : ℝ)) + Real.log z.den) := by
      field_simp [hNr]
    _ = _ := by
      rw [Real.sqrt_div_self]
      ring

theorem smallOddPrimeError_div_sq_tendsto_zero (z : ℚ) :
    Tendsto (fun N : ℕ => smallOddPrimeError z N / (n N : ℝ) ^ 2) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := ((hi.const_mul (6 * Real.log 65 + Real.log z.den)).add
    (log_nat_div_sqrt_tendsto_zero.const_mul 6)).const_mul (2 * Real.sqrt 65 / 48)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (smallOddPrimeError_div_sq_eq z hN).symm

theorem smallOddPrimeContribution_eventually_lower (z : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      -ε ≤ smallOddPrimeContribution z N / (n N : ℝ) ^ 2 := by
  have he : ∀ᶠ N : ℕ in atTop, smallOddPrimeError z N / (n N : ℝ) ^ 2 < ε :=
    (tendsto_order.mp (smallOddPrimeError_div_sq_tendsto_zero z)).2 ε hε
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N heN hN
  have hsum := div_le_div_of_nonneg_right (smallOddPrimeContribution_lower z hN)
    (sq_nonneg (n N : ℝ))
  have hneg : -ε ≤ -(smallOddPrimeError z N / (n N : ℝ) ^ 2) :=
    neg_le_neg (le_of_lt heN)
  exact hneg.trans (by simpa only [neg_div] using hsum)

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem smallOddPrimeCutoff_bounds {N : ℕ} (hN : 0 < N) :
    2 ≤ 2 * Real.sqrt (H N) ∧ 2 * Real.sqrt (H N) ≤ (H N : ℝ) := by
  have hH : (4 : ℝ) ≤ (H N : ℝ) := by
    exact_mod_cast (show 4 ≤ H N by unfold H; omega)
  have hs : 2 ≤ Real.sqrt (H N) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (H N))
  constructor
  · linarith
  · nlinarith [mul_nonneg (Real.sqrt_nonneg (H N)) (sub_nonneg.mpr hs)]

theorem smallOddPrimes_eq_filter_H {N : ℕ} (hN : 0 < N) :
    smallOddPrimes N = (Finset.Ioc 0 (H N)).filter
      (fun p : ℕ => p.Prime ∧ p ≠ 2 ∧ (p : ℝ) ≤ 2 * Real.sqrt (H N)) := by
  ext p
  rw [mem_smallOddPrimes_iff]
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hprime, hp2, hp⟩
    have hpH : p ≤ H N := by
      exact_mod_cast hp.trans (smallOddPrimeCutoff_bounds hN).2
    exact ⟨⟨hprime.pos, hpH⟩, hprime, hp2, hp⟩
  · rintro ⟨_, hprime, hp2, hp⟩
    exact ⟨hprime, hp2, hp⟩

theorem oddPrimeContribution_split (z : ℚ) {N : ℕ} (hN : 0 < N) :
    (∑ p ∈ (Finset.Ioc 0 (H N)).filter (fun p => p.Prime ∧ p ≠ 2),
      (padicValRat p (determinantRat z N) : ℝ) * Real.log p) =
    smallOddPrimeContribution z N +
      ∑ p ∈ (Finset.Ioc 0 (H N)).filter
          (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
        (padicValRat p (determinantRat z N) : ℝ) * Real.log p := by
  classical
  unfold smallOddPrimeContribution
  rw [smallOddPrimes_eq_filter_H hN]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hprime : p.Prime
  · by_cases hcut : (p : ℝ) ≤ 2 * Real.sqrt (H N)
    · simp [hprime, hcut, not_lt.mpr hcut]
    · have hp2 : p ≠ 2 := by
        intro heq
        subst p
        exact hcut (by simpa only [Nat.cast_ofNat] using (smallOddPrimeCutoff_bounds hN).1)
      simp [hprime, hcut, lt_of_not_ge hcut, hp2]
  · simp [hprime]

end InternalCatalan

end

end OAI
