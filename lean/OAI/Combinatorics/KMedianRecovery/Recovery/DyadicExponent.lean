import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.UniformBits

namespace OAI

namespace MetricKMedianRecovery.Categorical

noncomputable def dyadicExponent (x : ℝ) : ℕ := Nat.clog 2 (Nat.ceil x)

lemma dyadic_round_bounds {x : ℝ} (hx : 1 ≤ x) :
    x ≤ ((2 ^ dyadicExponent x : ℕ) : ℝ) ∧
      ((2 ^ dyadicExponent x : ℕ) : ℝ) < 2*x := by
  have hlo : x ≤ ((2 ^ dyadicExponent x : ℕ) : ℝ) :=
    (Nat.le_ceil x).trans (Nat.cast_le.mpr (Nat.le_pow_clog (by decide) _))
  refine ⟨hlo, ?_⟩
  by_cases hn : 1 < Nat.ceil x
  · have hb : 0 < dyadicExponent x := Nat.clog_pos (by decide) hn
    have hprev : ((2^(dyadicExponent x-1) : ℕ):ℝ) < x :=
      (Nat.lt_ceil).mp (Nat.pow_pred_clog_lt_self (by decide) hn)
    have he : dyadicExponent x = (dyadicExponent x-1)+1 := by omega
    rw [he, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  · have hceil : Nat.ceil x ≤ 1 := by omega
    have hb : dyadicExponent x = 0 := Nat.clog_of_right_le_one hceil 2
    rw [hb]
    norm_num
    linarith

noncomputable def tolerance (epsilon : ℝ) : ℝ :=
  1 / ((2 ^ dyadicExponent (max (4/epsilon) 8) : ℕ) : ℝ)

lemma tolerance_spec {epsilon : ℝ} (he : 0 < epsilon) :
    0 < tolerance epsilon ∧
    min (epsilon/8) (1/16) ≤ tolerance epsilon ∧
    tolerance epsilon ≤ min (epsilon/4) (1/8) := by
  have hx : (1:ℝ) ≤ max (4/epsilon) 8 := le_trans (by norm_num) (le_max_right _ _)
  obtain ⟨hlo,hhi⟩ := dyadic_round_bounds hx
  have hp : (0:ℝ) < (2 ^ dyadicExponent (max (4/epsilon) 8) : ℕ) := by positivity
  refine ⟨by exact div_pos (by norm_num) hp, ?_, ?_⟩
  · unfold tolerance
    apply (le_div_iff₀ hp).mpr
    by_cases hb : 4/epsilon ≤ 8
    · rw [max_eq_right hb] at *
      have hm : min (epsilon/8) (1/16) ≤ (1:ℝ)/16 := min_le_right _ _
      have hm' := mul_le_mul_of_nonneg_right hm hp.le
      nlinarith
    · have hb' : 8 ≤ 4/epsilon := (le_of_not_ge hb)
      rw [max_eq_left hb'] at *
      have hm : min (epsilon/8) (1/16) ≤ epsilon/8 := min_le_left _ _
      have hm' := mul_le_mul_of_nonneg_right hm hp.le
      have he' : epsilon*(4/epsilon) = 4 := by field_simp
      have hh := mul_lt_mul_of_pos_left hhi he
      nlinarith
  · unfold tolerance
    apply le_min
    · apply (div_le_iff₀ hp).mpr
      have hh := le_trans (le_max_left (4/epsilon) 8) hlo
      have hh' := mul_le_mul_of_nonneg_left hh he.le
      have he' : epsilon*(4/epsilon) = 4 := by field_simp
      nlinarith
    · apply (div_le_iff₀ hp).mpr
      have hh := le_trans (le_max_right (4/epsilon) 8) hlo
      linarith

end MetricKMedianRecovery.Categorical

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

noncomputable def stepExponent (a : ℕ) (epsilon : ℝ) : ℕ :=
  dyadicExponent ((a:ℝ)^2 / tolerance epsilon)

noncomputable def sampleCount (q a : ℕ) (epsilon : ℝ) : ℕ :=
  Nat.ceil ((((2 ^ stepExponent a epsilon : ℕ) : ℝ) * q * (a:ℝ)^2) /
    (4 * tolerance epsilon ^ 3))

lemma stepExponent_spec {a : ℕ} {epsilon : ℝ} (ha : 0 < a) (he : 0 < epsilon) :
    (a:ℝ)^2 ≤ tolerance epsilon * (2^stepExponent a epsilon:ℕ) ∧
    ((2^stepExponent a epsilon:ℕ):ℝ) < 2*(a:ℝ)^2 / tolerance epsilon := by
  obtain ⟨ht,_,htu⟩ := tolerance_spec he
  have ha1 : (1:ℝ) ≤ a := Nat.one_le_cast.mpr ha
  have ht1 : tolerance epsilon ≤ 1 := (htu.trans (min_le_right _ _)).trans (by norm_num)
  have hx : 1 ≤ (a:ℝ)^2 / tolerance epsilon := by
    apply (le_div_iff₀ ht).mpr
    nlinarith
  obtain ⟨hlo,hhi⟩ := dyadic_round_bounds hx
  change (a:ℝ)^2 / tolerance epsilon ≤ ((2^stepExponent a epsilon:ℕ):ℝ) at hlo
  change ((2^stepExponent a epsilon:ℕ):ℝ) < 2*((a:ℝ)^2 / tolerance epsilon) at hhi
  exact ⟨by nlinarith [(div_le_iff₀ ht).mp hlo], by simpa only [mul_div_assoc] using hhi⟩

lemma sampleCount_spec {q a : ℕ} {epsilon : ℝ}
    (hq : 0 < q) (ha : 0 < a) (he : 0 < epsilon) :
    0 < sampleCount q a epsilon ∧
    (((2^stepExponent a epsilon:ℕ):ℝ)*q*(a:ℝ)^2 /
      (4*tolerance epsilon^3) ≤ sampleCount q a epsilon) ∧
    (sampleCount q a epsilon:ℝ) < (q:ℝ)*(a:ℝ)^4 /
      (2*tolerance epsilon^4) + 1 := by
  have ht := (tolerance_spec he).1
  have htcount : 0 < (((2^stepExponent a epsilon:ℕ):ℝ)*q*(a:ℝ)^2 /
      (4*tolerance epsilon^3)) := by positivity
  have hpos : 0 < sampleCount q a epsilon := Nat.ceil_pos.mpr htcount
  have hlo : (((2^stepExponent a epsilon:ℕ):ℝ)*q*(a:ℝ)^2 /
      (4*tolerance epsilon^3)) ≤ sampleCount q a epsilon := Nat.le_ceil _
  refine ⟨hpos, hlo, ?_⟩
  have hceil := Nat.ceil_lt_add_one htcount.le
  have hb := (stepExponent_spec ha he).2
  have hh := mul_lt_mul_of_pos_right hb (show 0 < (q:ℝ)*(a:ℝ)^2 by positivity)
  have hdiv := div_lt_div_of_pos_right hh (show 0 < 4*tolerance epsilon^3 by positivity)
  have hid : (2*(a:ℝ)^2/tolerance epsilon*((q:ℝ)*(a:ℝ)^2)) /
      (4*tolerance epsilon^3) = (q:ℝ)*(a:ℝ)^4/(2*tolerance epsilon^4) := by
    field_simp
    ring
  rw [hid] at hdiv
  change (sampleCount q a epsilon:ℝ) < _ at hceil
  rw [← mul_assoc] at hdiv
  linarith only [hceil,hdiv]

noncomputable def sampledCategorical {E : Type*} [Fintype E] [DecidableEq E]
    {a : ℕ} (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (epsilon : ℝ)
    (bits : BinaryOracleIndex E a (stepExponent a epsilon)
      (sampleCount (Fintype.card E) a epsilon) → Bool) : Finset E :=
  binaryGreedyOutput part hp g bits

lemma sampledCategorical_feasible {E : Type*} [Fintype E] [DecidableEq E]
    {a : ℕ} (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (epsilon : ℝ)
    (bits : BinaryOracleIndex E a (stepExponent a epsilon)
      (sampleCount (Fintype.card E) a epsilon) → Bool) :
    PartitionFeasible part (sampledCategorical part hp g epsilon bits) :=
  binaryGreedyOutput_feasible part hp g bits

lemma sampledCategorical_expected {E : Type*} [Fintype E] [DecidableEq E]
    {a : ℕ} (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {epsilon : ℝ} (he : 0 < epsilon) (S : Finset E) (hS : PartitionFeasible part S) :
    (1 - 1/Real.exp 1 - epsilon) * g S ≤
      average (fun bits : BinaryOracleIndex E a (stepExponent a epsilon)
          (sampleCount (Fintype.card E) a epsilon) → Bool =>
        g (sampledCategorical part hp g epsilon bits)) := by
  by_cases ha : 0 < a
  · have hq : 0 < Fintype.card E := by
      obtain ⟨e,_⟩ := hp ⟨0,ha⟩
      exact Fintype.card_pos_iff.mpr ⟨e⟩
    obtain ⟨ht,_,htu⟩ := tolerance_spec he
    obtain ⟨hL,hcount,_⟩ := sampleCount_spec hq ha he
    have h := binaryGreedyOutput_expected part hp g hmono hsub hg0 ha ht
      (htu.trans (min_le_right _ _)) (stepExponent_spec ha he).1 hL hcount S hS
    have hgn : 0 ≤ g S := by rw [← hg0]; exact hmono (Finset.empty_subset _)
    have heps : 4*tolerance epsilon ≤ epsilon := by
      have := htu.trans (min_le_left _ _)
      linarith
    exact (mul_le_mul_of_nonneg_right (by linarith :
      1-1/Real.exp 1-epsilon ≤ 1-1/Real.exp 1-4*tolerance epsilon) hgn).trans h
  · have ha0 : a = 0 := by omega
    have hE : IsEmpty E := ⟨fun e => by have := (part e).isLt; omega⟩
    have hSe : S = ∅ := Subsingleton.elim _ _
    rw [hSe,hg0,mul_zero]
    apply average_nonneg
    intro bits
    rw [Subsingleton.elim (sampledCategorical part hp g epsilon bits) ∅,hg0]

end MetricKMedianRecovery.Categorical

end OAI
