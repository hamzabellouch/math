import OAI.NumberTheory.TwoPointCorrelations.HalaszPrimeTheta
import OAI.NumberTheory.TwoPointCorrelations.MRTSmoothDistance

namespace OAI

/-! Prime discrepancy for the near-minimizing twist in MRT Appendix A.
The deleted-prime contribution is kept separate in Cauchy--Schwarz; this
retains the strict exponent needed by the renormalization error. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped ComplexConjugate Classical

noncomputable def halaszPrimeDiscrepancy (F : ℕ → ℂ) (t : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / p

lemma halasz_one_sub_norm_sq {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖1 - z‖ ^ 2 ≤ 2 * (1 - z.re) := by
  have hs : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im] at hs ⊢
  nlinarith

lemma halasz_prime_unit_bound (F : ℕ → ℂ) (hF : OneBounded F)
    (t : ℝ) {N p : ℕ} (hp : p ∈ primesUpTo N) :
    ‖F p * conj (mrtArchimedeanTwist t p)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_conj, mrtArchimedeanTwist_norm, mul_one]
  exact hF p (mem_filter.mp hp).2.pos

lemma halasz_masked_discrepancy_split (F : ℕ → ℂ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (t : ℝ) (N : ℕ) :
    halaszPrimeDiscrepancy (mrtMissingCoefficient F Q) t N =
      (∑ p ∈ (primesUpTo N).filter (fun p => p ∈ Q), (1 : ℝ) / p) +
      ∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q),
        ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / p := by
  unfold halaszPrimeDiscrepancy
  rw [← sum_filter_add_sum_filter_not (primesUpTo N) (fun p => p ∈ Q)]
  congr 1 <;> apply sum_congr rfl
  · intro p hp
    obtain ⟨hpN, hpQ⟩ := mem_filter.mp hp
    rw [mrtMissingCoefficient, mrtPrimeMask_prime Q hQ (mem_filter.mp hpN).2,
      ite_eq_left hpQ]
    simp
  · intro p hp
    obtain ⟨hpN, hpQ⟩ := mem_filter.mp hp
    rw [mrtMissingCoefficient, mrtPrimeMask_prime Q hQ (mem_filter.mp hpN).2,
      ite_eq_right hpQ]
    simp

lemma halasz_undeleted_discrepancy_sq (F : ℕ → ℂ) (hF : OneBounded F)
    (Q : Finset ℕ) (t : ℝ) (N : ℕ) :
    (∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q),
      ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / p) ^ 2 ≤
      2 * (∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q), (1 : ℝ) / p) *
        squaredDistance F (mrtArchimedeanTwist t) N := by
  let S := (primesUpTo N).filter (fun p => p ∉ Q)
  have hdef (p : ℕ) (hp : p ∈ primesUpTo N) :
      0 ≤ 1 - (F p * conj (mrtArchimedeanTwist t p)).re :=
    sub_nonneg.mpr ((Complex.re_le_norm _).trans (halasz_prime_unit_bound F hF t hp))
  have hh := sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (r := fun p => ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / (p : ℝ))
    (f := fun p => (1 : ℝ) / p)
    (g := fun p => 2 * (1 - (F p * conj (mrtArchimedeanTwist t p)).re) / p)
    (fun _ _ => by positivity)
    (fun p hp => div_nonneg (mul_nonneg (by norm_num) (hdef p (mem_filter.mp hp).1))
      (Nat.cast_nonneg p)) (fun p hp => ?_)
  · have hd : (∑ p ∈ S, (1 - (F p * conj (mrtArchimedeanTwist t p)).re) / p) ≤
        squaredDistance F (mrtArchimedeanTwist t) N := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro p hp _
      exact div_nonneg (hdef p hp) (Nat.cast_nonneg p)
    have he : (∑ p ∈ S, 2 * (1 - (F p * conj (mrtArchimedeanTwist t p)).re) / p) =
        2 * ∑ p ∈ S, (1 - (F p * conj (mrtArchimedeanTwist t p)).re) / p := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    rw [he] at hh
    exact hh.trans (by
      have h := mul_le_mul_of_nonneg_left hd
        (show 0 ≤ 2 * ∑ p ∈ S, (1 : ℝ) / p by positivity)
      convert h using 1
      ring)
  · have hsq := halasz_one_sub_norm_sq (halasz_prime_unit_bound F hF t (mem_filter.mp hp).1)
    rw [div_pow]
    apply (div_le_div_of_nonneg_right hsq (sq_nonneg (p : ℝ))).trans_eq
    ring

lemma halasz_near_discrepancy_numeric (L A B Z D : ℝ) (hL : 0 ≤ L)
    (hAB : A ≤ B)
    (hAhi : A ≤ 51 / 100 * L) (hBhi : B ≤ 101 / 100 * L)
    (hD : D ≤ L / 8) (hZsq : Z ^ 2 ≤ 2 * (B - A) * D) :
    A + Z ≤ 7 / 8 * L := by
  have hm := mul_le_mul_of_nonneg_left hD (by linarith : 0 ≤ 2 * (B - A))
  have hprod : 0 ≤ (A - 51 / 100 * L) * (A - 99 / 100 * L) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  by_contra hh
  have hz : 7 / 8 * L - A < Z := by linarith
  have hz0 : 0 ≤ 7 / 8 * L - A := by linarith
  have hs := mul_self_lt_mul_self hz0 hz
  nlinarith

/-- The `7/8` prime-discrepancy estimate used for near-twist renormalization.
Only primes below the actual Appendix-A cutoff may be deleted. -/
theorem halasz_near_masked_discrepancy :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), OneBounded F →
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) N ≤
        Real.log (Real.log N) / 8 →
      halaszPrimeDiscrepancy (mrtMissingCoefficient F Q) t N ≤
        7 / 8 * Real.log (Real.log N) := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll := (Real.tendsto_log_atTop.comp hlog).eventually
    (eventually_ge_atTop (100 * |C|))
  filter_upwards [hlog.eventually (eventually_ge_atTop (4 : ℝ)), hll] with N hl hllN
  dsimp only [Function.comp_def] at hllN
  intro F hF Q hQ hcut t hD
  let L := Real.log (Real.log N)
  let A := ∑ p ∈ (primesUpTo N).filter (fun p => p ∈ Q), (1 : ℝ) / p
  let B := ∑ p ∈ primesUpTo N, (1 : ℝ) / p
  let Z := ∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q),
    ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / p
  have hL : 0 ≤ L := by dsimp [L]; linarith [abs_nonneg C]
  have hCsmall : C ≤ L / 100 := by dsimp [L]; linarith [le_abs_self C]
  have hN1 : 1 < (N : ℝ) := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hN2 : (2 : ℝ) ≤ N := by
    have : 2 ≤ N := by exact_mod_cast hN1
    exact_mod_cast this
  have hB : B ≤ 101 / 100 * L := by
    have hh := (abs_le.mp (hC N hN2)).2
    rw [mrt_sievePrimesUpTo_nat] at hh
    dsimp [B, L]
    linarith
  have hsqrt : 2 ≤ Real.sqrt (Real.log N) := by
    have hs := Real.sq_sqrt (by linarith : 0 ≤ Real.log N)
    have hn := Real.sqrt_nonneg (Real.log N)
    nlinarith
  have hY2 : 2 ≤ Real.exp (Real.sqrt (Real.log N)) := by
    linarith [Real.add_one_le_exp (Real.sqrt (Real.log N))]
  have hA : A ≤ 51 / 100 * L := by
    have hsub : (primesUpTo N).filter (fun p => p ∈ Q) ⊆
        sievePrimesUpTo (Real.exp (Real.sqrt (Real.log N))) := by
      intro p hp
      obtain ⟨hpN, hpQ⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff (by positivity)).mpr
        (hcut p hpQ)), (mem_filter.mp hpN).2⟩
    have ha := sum_le_sum_of_subset_of_nonneg hsub
      (f := fun p : ℕ => (1 : ℝ) / p) (by intros; positivity)
    have hb := (abs_le.mp (hC _ hY2)).2
    rw [Real.log_exp, Real.log_sqrt (by linarith : 0 ≤ Real.log N)] at hb
    dsimp [A, L] at *
    linarith
  have hmass : (∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q), (1 : ℝ) / p) = B - A := by
    have hh := sum_filter_add_sum_filter_not (primesUpTo N) (fun p => p ∈ Q)
      (fun p : ℕ => (1 : ℝ) / p)
    dsimp [A, B]
    linarith
  have hAB : A ≤ B := by
    have hh : 0 ≤ ∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q), (1 : ℝ) / p := by positivity
    rw [hmass] at hh
    linarith
  have hZ := halasz_undeleted_discrepancy_sq F hF Q t N
  rw [hmass] at hZ
  have hh := halasz_near_discrepancy_numeric L A B Z
    (squaredDistance F (mrtArchimedeanTwist t) N) hL hAB hA hB hD hZ
  simpa only [halasz_masked_discrepancy_split F Q hQ t N, A, Z] using hh

end TwoPointCorrelations

end OAI
