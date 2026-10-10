import OAI.NumberTheory.JointDickman.Amplification.IntegerRationalSum

namespace OAI

/-! # Uniform rational partial sums down to the trivial range -/
namespace JointDickman
open Finset

lemma bounded_real_additive_sum (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (N : ℕ) (θ : ℝ) :
    ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖(f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, (1:ℝ) := by
      apply sum_le_sum
      intro n hn
      simpa only [norm_mul,norm_additivePhase,mul_one,Complex.norm_real,Real.norm_eq_abs] using hf n
    _ = _ := by simp

theorem squarefree_rational_uniform_partial_sums : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n=0) → ∀ (N B q : ℕ) (u : ℤ),
    0 < N → 2 ≤ B → (80:ℝ)*Real.log B ≤ B →
    (B:ℝ)/2 ≤ Real.log N → Real.log N ≤ 3*(B:ℝ) →
    0 < q → u.natAbs.Coprime q → (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^10 →
    ∀ M ≤ N, ‖∑ n ∈ Ioc 0 M, (f n:ℂ)*additivePhase ((n:ℝ)*((u:ℝ)/q))‖ ≤
      C*N*(1+Real.log B)/(B:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := squarefree_integer_rational_polylog_sum_bound
  refine ⟨1+4*C,by positivity,?_⟩
  intro f hf hb hs N B q u hN hB hlogB hloglo hloghi hq hu hqlo hqhi M hMN
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hBR : (0:ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hB1 : (1:ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB1
  let T := (N:ℝ)*(1+Real.log B)/(B:ℝ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  by_cases hsmall : (M:ℝ) ≤ (N:ℝ)/(B:ℝ)^2
  · have htriv := bounded_real_additive_sum f hb M ((u:ℝ)/q)
    have hscale : (N:ℝ)/(B:ℝ)^2 ≤ T := by
      dsimp [T]
      apply (div_le_div_iff₀ (pow_pos hBR 2) hBR).mpr
      have hBB : (B:ℝ) ≤ (B:ℝ)^2 := le_self_pow₀ hB1 (by norm_num : 2 ≠ 0)
      nlinarith [mul_nonneg hlB (sq_nonneg (B:ℝ))]
    have hCT : T ≤ (1+4*C)*T := by nlinarith
    convert htriv.trans (hsmall.trans (hscale.trans hCT)) using 1
    dsimp [T]
    ring
  have hMlo : (N:ℝ)/(B:ℝ)^2 ≤ M := (lt_of_not_ge hsmall).le
  have hMR : (0:ℝ) < M := (div_pos hNR (pow_pos hBR 2)).trans_le hMlo
  have hlogM : (B:ℝ)/4 ≤ Real.log M := by
    have hh := Real.log_le_log (div_pos hNR (pow_pos hBR 2)) hMlo
    rw [Real.log_div hNR.ne' (pow_ne_zero 2 hBR.ne'),Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hBM : B^20 ≤ M := by
    have hpow : (0:ℝ) < (B:ℝ)^20 := pow_pos hBR 20
    have hlogpow : Real.log ((B:ℝ)^20) ≤ Real.log M := by
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith
    have he := (Real.log_le_log_iff hpow hMR).mp hlogpow
    exact_mod_cast he
  have hqM : (q:ℝ) ≤ (M:ℝ)/(B:ℝ)^8 := by
    calc
      _ ≤ (N:ℝ)/(B:ℝ)^10 := hqhi
      _ = ((N:ℝ)/(B:ℝ)^2)/(B:ℝ)^8 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hMlo (pow_nonneg hBR.le 8)
  have hlogMhi : Real.log M ≤ 3*(B:ℝ) :=
    (Real.log_le_log hMR (by exact_mod_cast hMN)).trans hloghi
  have h := hbound f hf hb hs M B q u hB hBM hq hu hlogMhi hqlo hqM
  have hmain : C*M*(1+Real.log B)/Real.log M ≤ 4*C*T := by
    calc
      _ ≤ C*N*(1+Real.log B)/((B:ℝ)/4) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by positivity) hlogM
      _ = _ := by dsimp [T]; ring
  have hCT : 4*C*T ≤ (1+4*C)*T := by nlinarith
  convert h.trans (hmain.trans hCT) using 1
  dsimp [T]
  ring

end JointDickman

end OAI
