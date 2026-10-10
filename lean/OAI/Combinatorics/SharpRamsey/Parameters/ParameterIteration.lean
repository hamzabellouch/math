import Mathlib

namespace OAI

section
namespace SharpLogRamsey.ParameterIteration
open Real

theorem finite_contraction (D : ℕ→ℝ) (a b R : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hb' : b≤1/2) (h₀ : D 0≤R) (T : ℕ)
    (hstep : ∀ i<T,D (i+1)≤a+b*D i) :
    D T≤2*a+b^T*R := by
  have hbound : ∀ i≤T,D i≤2*a+b^i*R := by
    intro i
    induction i with
    | zero => intro _; simpa only [pow_zero,one_mul] using h₀.trans (by linarith)
    | succ i ih =>
      intro hi
      have hd := ih (by omega)
      have hh := (hstep i (by omega)).trans (add_le_add_right (mul_le_mul_of_nonneg_left hd hb) a)
      have hac : a+2*a*b≤2*a := by nlinarith
      rw [pow_succ]
      nlinarith
  exact hbound T le_rfl

theorem source_contraction {σ β η : ℝ} (hσ : 1≤σ) (hβ : 0≤β)
    (hhalf : σ^(-η/4)≤1/2) (D : ℕ→ℝ) (T : ℕ)
    (hT : 1≤(T:ℝ)*η/4) (h₀ : D 0≤σ)
    (hstep : ∀ i<T,D (i+1)≤σ^(2*β)+D i*σ^(-η/4)) :
    D T≤3*σ^(2*β) := by
  have hσ0 : 0<σ := lt_of_lt_of_le zero_lt_one hσ
  have ha : 1≤σ^(2*β) := one_le_rpow hσ (by positivity)
  have Hb := finite_contraction D (σ^(2*β)) (σ^(-η/4)) σ
    (rpow_nonneg hσ0.le _) (rpow_nonneg hσ0.le _) hhalf h₀ T (by
      intro i hi
      simpa only [mul_comm] using hstep i hi)
  have hpow : (σ^(-η/4))^T*σ=σ^(1-(T:ℝ)*η/4) := by
    rw [←rpow_natCast,←rpow_mul hσ0.le]
    conv_lhs => rhs; rw [←rpow_one σ]
    rw [←rpow_add hσ0]
    congr 1
    ring
  rw [hpow] at Hb
  have hsmall : σ^(1-(T:ℝ)*η/4)≤1 := rpow_le_one_of_one_le_of_nonpos hσ (by linarith)
  linarith

theorem eventual_half {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in Filter.atTop, σ^(-η/4)≤1/2 := by
  have ht : Filter.Tendsto (fun σ : ℝ=>σ^(-η/4)) Filter.atTop (nhds 0) := by
    simpa only [neg_div] using (tendsto_rpow_neg_atTop (show 0<η/4 by linarith))
  exact ht.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2))

theorem prescribed_count {η : ℝ} (hη : 0<η) :
    1≤(⌈8/η⌉₊:ℝ)*η/4 := by
  have h := Nat.le_ceil (8/η)
  have hh := mul_le_mul_of_nonneg_right h hη.le
  have he : (8/η)*η=(8:ℝ) := div_mul_cancel₀ 8 (ne_of_gt hη)
  rw [he] at hh
  linarith

end SharpLogRamsey.ParameterIteration

end

end OAI
