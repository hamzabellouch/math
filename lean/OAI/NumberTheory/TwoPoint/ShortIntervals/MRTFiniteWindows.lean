import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortEnergy
import OAI.NumberTheory.TwoPoint.PublishedInputs
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDyadicMeanSquare

namespace OAI

/-! The finite-support Fourier estimate applies to short exponential
sums with exact floor endpoints. -/

namespace TwoPointCorrelations

open MeasureTheory Finset Set
open scoped Classical

lemma mrt_finite_window_eq_short_sum (b : ℕ → ℂ) {N H : ℕ}
    (hHN : H ≤ N) {x : ℝ} (hx : x ∈ Icc (N:ℝ) (2*N)) (α : ℝ) :
    mrtIntervalSum (Finset.Ioc N (4*N)) (fun n => b n * additiveCharacter α n)
      x H = shortExponentialSum b H α x := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg N).trans hx.1
  have hxH : 0 ≤ x+(H:ℝ) := add_nonneg hx0 (Nat.cast_nonneg H)
  have hfilter : (Finset.Ioc N (4*N)).filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) ≤ x+H) =
      Finset.Icc (Nat.floor x+1) (Nat.floor (x+(H:ℝ))) := by
    ext n
    simp only [mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨_, hnlo, hnhi⟩
      exact ⟨Nat.succ_le_iff.mpr ((Nat.floor_lt hx0).mpr hnlo),
        (Nat.le_floor_iff hxH).mpr hnhi⟩
    · rintro ⟨hnlo, hnhi⟩
      have hnrlo : x < (n:ℝ) := (Nat.floor_lt hx0).mp (by omega)
      have hnrhi : (n:ℝ) ≤ x+H := (Nat.le_floor_iff hxH).mp hnhi
      have hNr : (N:ℝ) < n := hx.1.trans_lt hnrlo
      have hHNr : (H:ℝ) ≤ N := by exact_mod_cast hHN
      have hn4 : (n:ℝ) ≤ (4*N:ℕ) := by push_cast; nlinarith [hx.2]
      exact ⟨⟨by exact_mod_cast hNr, by exact_mod_cast hn4⟩, hnrlo, hnrhi⟩
  unfold mrtIntervalSum
  rw [← sum_filter, hfilter]
  rfl

theorem mrt_literal_short_energy (b : ℕ → ℂ) {N H : ℕ} (hH : 0 < H) (hHN : H ≤ N) :
    (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum b H 0 x‖^2) /
        ((N:ℝ)*(H:ℝ)^2) ≤
      (69984/(2*Real.pi)) *
        ∫ t : ℝ, mrtShortKernel ((N:ℝ)/H) t *
          ‖mrtExponentialPolynomial (Finset.Ioc N (4*N)) (fun n => b n/(n:ℂ))
            (fun n => -Real.log (n:ℝ)) t‖^2 := by
  have hN : 0 < N := lt_of_lt_of_le hH hHN
  have hn : ∀ n ∈ Finset.Ioc N (4*N), 0 < n :=
    fun n hn => lt_trans hN (Finset.mem_Ioc.mp hn).1
  have he (x : ℝ) (hx : x ∈ Icc (N:ℝ) (2*N)) :
      mrtIntervalSum (Finset.Ioc N (4*N)) b x H = shortExponentialSum b H 0 x := by
    simpa only [additiveCharacter, mul_zero, zero_mul, Complex.ofReal_zero,
      Complex.exp_zero, mul_one] using mrt_finite_window_eq_short_sum b hHN hx 0
  have hh := mrt_normalized_short_energy (Finset.Ioc N (4*N)) hn b (N := (N:ℝ)) (h := (H:ℝ))
    (by exact_mod_cast hN) (by exact_mod_cast hH) (by exact_mod_cast hHN)
  have hleft : (∫ x in (N:ℝ)..(2*N), ‖mrtIntervalSum (Finset.Ioc N (4*N)) b x H‖^2) =
      ∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum b H 0 x‖^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)] : (N:ℝ) ≤ 2*N)] at hx
    change ‖mrtIntervalSum (Finset.Ioc N (4*N)) b x H‖^2 =
      ‖shortExponentialSum b H 0 x‖^2
    rw [he x hx]
  rw [hleft] at hh
  simpa only [mrt_log_dirichlet_polynomial _ hn] using hh

lemma mrt_log_dirichlet_two_dyadic (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N) (t : ℝ) :
    mrtLogDirichlet (Finset.Ioc N (4*N)) b t =
      mrtDyadicPolynomial b N t + mrtDyadicPolynomial b (2*N) t := by
  have hn : ∀ n ∈ Finset.Ioc N (4*N), 0 < n :=
    fun n hn => lt_trans hN (Finset.mem_Ioc.mp hn).1
  rw [mrt_log_dirichlet_polynomial _ hn]
  have hs : Finset.Ioc N (4*N) = Finset.Ioc N (2*N) ∪ Finset.Ioc (2*N) (4*N) :=
    (Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)).symm
  have hd : Disjoint (Finset.Ioc N (2*N)) (Finset.Ioc (2*N) (4*N)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have := (Finset.mem_Ioc.mp hn).2
    have := (Finset.mem_Ioc.mp hn').1
    omega
  simp only [mrtDyadicPolynomial, mrtExponentialPolynomial]
  rw [show 2*(2*N) = 4*N by omega, hs, sum_union hd]

theorem mrt_literal_short_energy_dyadic (b : ℕ → ℂ) {N H : ℕ}
    (hH : 0 < H) (hHN : H ≤ N) :
    (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum b H 0 x‖^2) /
        ((N:ℝ)*(H:ℝ)^2) ≤
      (139968/(2*Real.pi)) *
        ((∫ t : ℝ, mrtShortKernel ((N:ℝ)/H) t * ‖mrtDyadicPolynomial b N t‖^2) +
          ∫ t : ℝ, mrtShortKernel ((N:ℝ)/H) t * ‖mrtDyadicPolynomial b (2*N) t‖^2) := by
  have hN : 0 < N := lt_of_lt_of_le hH hHN
  have hn (n k : ℕ) (hk : 0 < k) (hn : n ∈ Finset.Ioc k (2*k)) : 0 < n :=
    lt_trans hk (Finset.mem_Ioc.mp hn).1
  have hid (k : ℕ) (hk : 0 < k) :
      Integrable (fun t => mrtShortKernel ((N:ℝ)/H) t * ‖mrtDyadicPolynomial b k t‖^2) := by
    have hi := mrt_short_kernel_integrable (Finset.Ioc k (2*k)) b ((N:ℝ)/H)
    simpa only [mrt_log_dirichlet_polynomial _ (fun n hn' => hn n k hk hn'),
      mrtDyadicPolynomial] using hi
  have hi := integral_mono (mrt_short_kernel_integrable (Finset.Ioc N (4*N)) b ((N:ℝ)/H))
    (((hid N hN).const_mul 2).add ((hid (2*N) (by omega)).const_mul 2)) (fun t => by
      change mrtShortKernel ((N:ℝ)/H) t * ‖mrtLogDirichlet (Finset.Ioc N (4*N)) b t‖^2 ≤
        2*(mrtShortKernel ((N:ℝ)/H) t * ‖mrtDyadicPolynomial b N t‖^2) +
          2*(mrtShortKernel ((N:ℝ)/H) t * ‖mrtDyadicPolynomial b (2*N) t‖^2)
      rw [mrt_log_dirichlet_two_dyadic b hN]
      have he := norm_add_le (mrtDyadicPolynomial b N t) (mrtDyadicPolynomial b (2*N) t)
      have hp := pow_le_pow_left₀ (norm_nonneg _) he 2
      have hsq : ‖mrtDyadicPolynomial b N t + mrtDyadicPolynomial b (2*N) t‖^2 ≤
          2*‖mrtDyadicPolynomial b N t‖^2 + 2*‖mrtDyadicPolynomial b (2*N) t‖^2 := by
        nlinarith [sq_nonneg (‖mrtDyadicPolynomial b N t‖-‖mrtDyadicPolynomial b (2*N) t‖)]
      have hk0 : 0 ≤ mrtShortKernel ((N:ℝ)/H) t := le_min (by norm_num) (by positivity)
      simpa only [mul_add, mul_left_comm] using mul_le_mul_of_nonneg_left hsq hk0)
  simp only [Pi.add_apply] at hi
  rw [integral_add ((hid N hN).const_mul 2) ((hid (2*N) (by omega)).const_mul 2),
    integral_const_mul, integral_const_mul] at hi
  have hb := mrt_normalized_short_energy (Finset.Ioc N (4*N))
    (fun n hn' => lt_trans hN (Finset.mem_Ioc.mp hn').1) b
    (N := (N:ℝ)) (h := (H:ℝ))
    (by exact_mod_cast hN) (by exact_mod_cast hH) (by exact_mod_cast hHN)
  have hl : (∫ x in (N:ℝ)..(2*N), ‖mrtIntervalSum (Finset.Ioc N (4*N)) b x H‖^2) =
      ∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum b H 0 x‖^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)] : (N:ℝ) ≤ 2*N)] at hx
    have he := mrt_finite_window_eq_short_sum b hHN hx 0
    simpa only [additiveCharacter, mul_zero, zero_mul, Complex.ofReal_zero,
      Complex.exp_zero, mul_one] using congrArg (fun z : ℂ => ‖z‖^2) he
  rw [hl] at hb
  calc
    _ ≤ _ := hb
    _ ≤ _ := (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)

end TwoPointCorrelations

end OAI
