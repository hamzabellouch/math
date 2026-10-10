import OAI.NumberTheory.JointDickman.Analysis.MellinSieveScale

namespace OAI

/-! # Uniform divisor-kernel errors on polynomial frequency ranges -/
namespace JointDickman

lemma mellin_integer_dyadic_scale (q : ℕ) (hq : 0 < q) :
    q^12 ≤ 2^(Nat.log 2 (q^3)+1)*q^9 ∧
      2^(Nat.log 2 (q^3)+1)*q^9 ≤ 2*q^12 := by
  have hlo := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (q^3)).le
  have hhi := Nat.pow_log_le_self 2 (pow_ne_zero 3 hq.ne')
  constructor
  · convert Nat.mul_le_mul_right (q^9) hlo using 1; ring
  · rw [pow_succ]
    have hh := Nat.mul_le_mul_right (2*q^9) hhi
    convert hh using 1 <;> ring

lemma mellin_integer_frequency_scale (q : ℕ) (hq : 16 ≤ q) {t : ℝ}
    (ht : (q:ℝ)^7 ≤ |t|) :
    (((2^(Nat.log 2 (q^3)+1)*q^9:ℕ):ℝ))^(1/2:ℝ) ≤ |t/(2*Real.pi)| := by
  have hqR : (16:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hs := (mellin_integer_dyadic_scale q (by omega)).2
  have hsR : (((2^(Nat.log 2 (q^3)+1)*q^9:ℕ):ℝ)) ≤ 2*(q:ℝ)^12 := by exact_mod_cast hs
  have hroot : (((2^(Nat.log 2 (q^3)+1)*q^9:ℕ):ℝ))^(1/2:ℝ) ≤ 2*(q:ℝ)^6 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by positivity)]
    nlinarith [pow_nonneg hq0.le 12]
  apply hroot.trans
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi), le_div_iff₀ (by positivity)]
  have hp : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
  have h1 : 2*(q:ℝ)^6*(2*Real.pi) ≤ 16*(q:ℝ)^6 := by nlinarith [pow_nonneg hq0.le 6]
  have h2 : 16*(q:ℝ)^6 ≤ (q:ℝ)^7 := by
    calc
      16*(q:ℝ)^6 ≤ (q:ℝ)*(q:ℝ)^6 := mul_le_mul_of_nonneg_right hqR (pow_nonneg hq0.le 6)
      _ = (q:ℝ)^7 := by ring
  exact h1.trans (h2.trans ht)

/-- A uniform divisor estimate up to `q` over a polynomial frequency range,
with explicit level-dependent error. -/
theorem mellinSieve_integer_scale_uniform (B : ℝ) (hB : 1 ≤ B) :
    ∃ A δ V : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (q d : ℕ), 16 ≤ q → 0 < d → d ≤ q → V ≤ (q:ℝ)^9 →
      ∀ (N t : ℝ), (q:ℝ)^10 ≤ N → N ≤ (q:ℝ)^11 → |t| ≤ (q:ℝ)^B →
      ‖mellinSieveDiscreteKernel (q^12) d N t-mellinSieveMainKernel N t/(d:ℂ)‖ ≤
        6*(q:ℝ)^9 + (Nat.log 2 (q^3)+1:ℕ)*A*N^(1-δ) := by
  obtain ⟨A,δ,V,hA,hδ,hδ1,hhigh⟩ := mellinSieve_high_error B (by linarith)
  refine ⟨A,δ,V,hA,hδ,hδ1,?_⟩
  intro q d hq hd hdq hV N t hNlo hNhi ht
  have hqR : (16:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hN : 0 < N := (pow_pos hq0 10).trans_le hNlo
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdR : (d:ℝ) ≤ q := by exact_mod_cast hdq
  have hdN : (d:ℝ) ≤ N := hdR.trans ((le_self_pow₀ hq1 (by norm_num : 10 ≠ 0)).trans hNlo)
  have hrest : 0 ≤ (Nat.log 2 (q^3)+1:ℕ)*A*N^(1-δ) := by positivity
  by_cases htlow : |t| ≤ (q:ℝ)^7
  · exact (mellinSieve_integer_scale_low q d (by omega) hd hdq hNlo hNhi htlow).trans (le_add_of_nonneg_right hrest)
  have htbig : (q:ℝ)^7 ≤ |t| := le_of_not_ge htlow
  have hlo := mellin_integer_frequency_scale q hq htbig
  have hhi : |t/(2*Real.pi)| ≤ (((q^9:ℕ):ℝ))^B := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
    apply (div_le_self (abs_nonneg t) (by linarith [Real.pi_gt_three] : 1 ≤ 2*Real.pi)).trans
    apply ht.trans
    exact Real.rpow_le_rpow hq0.le (by
      simpa only [Nat.cast_pow] using le_self_pow₀ hq1 (by norm_num : 9 ≠ 0)) (by linarith)
  have hk : q^12/d ≤ 2^(Nat.log 2 (q^3)+1)*q^9 :=
    (Nat.div_le_self _ _).trans (mellin_integer_dyadic_scale q (by omega)).1
  have hh := hhigh N t d (q^12) (q^9) (Nat.log 2 (q^3)+1) hd hdN
    (pow_pos (by omega : 0 < q) 9) (by simpa only [Nat.cast_pow] using hV) hk hlo hhi
  have hs : (d:ℝ)*((q^9:ℕ):ℝ)^2/N ≤ (q:ℝ)^9 := by
    calc
      _ ≤ (q:ℝ)*((q:ℝ)^9)^2/(q:ℝ)^10 := by push_cast; gcongr
      _ = _ := by field_simp
  have hm : 4*N/((d:ℝ)*(4+t^2)) ≤ (q:ℝ)^9 := by
    have ht2 : (q:ℝ)^14 ≤ t^2 := by
      have hp := pow_le_pow_left₀ (pow_nonneg hq0.le 7) htbig 2
      simpa only [sq_abs, ← pow_mul] using hp
    have hq3 : (4:ℝ) ≤ (q:ℝ)^3 := by nlinarith [one_le_pow₀ hq1 (n := 2)]
    have hq14 : 4*(q:ℝ)^11 ≤ (q:ℝ)^14 := by
      have hp := mul_le_mul_of_nonneg_left hq3 (pow_nonneg hq0.le 11)
      convert hp using 1 <;> ring
    have hx : 4*N ≤ (d:ℝ)*(4+t^2) := by nlinarith [hNhi, hd1, sq_nonneg t]
    exact ((div_le_one (by positivity)).mpr hx).trans (one_le_pow₀ hq1)
  have hp : (N/(d:ℝ))^(1-δ) ≤ N^(1-δ) :=
    Real.rpow_le_rpow (by positivity) (div_le_self hN.le hd1) (by linarith)
  have hj : (Nat.log 2 (q^3)+1:ℕ)*A*(N/d)^(1-δ) ≤
      (Nat.log 2 (q^3)+1:ℕ)*A*N^(1-δ) := mul_le_mul_of_nonneg_left hp (by positivity)
  exact hh.trans (by linarith [pow_nonneg hq0.le 9])

end JointDickman

end OAI
