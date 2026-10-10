import OAI.Geometry.SurfaceImmersion.Correction.CorrectionScaleAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace OAI

/-! At each fixed order, all analytic smallness conditions and the
finite derivative budget hold below one positive scale threshold. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace ClosedSurfaceR4.ExactCorrection

lemma positive_power_threshold (c p b : ℝ) (hp : 0 < p) (hb : 0 < b) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < ε → c*t^p < b := by
  have hf : ContinuousAt (fun t : ℝ => c*t^p) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 p (Or.inr hp.le))
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), c*t^p < b :=
    hf.eventually (gt_mem_nhds (by simpa only [Real.zero_rpow hp.ne',mul_zero] using hb))
  obtain ⟨ε,hε,heε⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min ε 1,lt_min hε zero_lt_one,min_le_right _ _,?_⟩
  intro t ht hsmall
  apply heε
  simpa only [Real.dist_eq,sub_zero,abs_of_pos ht] using hsmall.trans_le (min_le_left ε 1)

theorem fixed_order_threshold (k : ℕ) (hk : 10 ≤ k)
    (ρ a η D B K : ℝ) (hρ : 0 < ρ) (ha : 0 < a) (hη : 0 < η)
    (_hD : 0 ≤ D) (_hB : 0 ≤ B) (_hK : 0 ≤ K) (C : ℕ → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < ε →
      t^(6/5 : ℝ)/t^(11/10 : ℝ) ≤ η ∧
      D*B*(t^(11/10 : ℝ)/t)^(40*(k+1)) ≤ min (ρ/4) (a/8) ∧
      (t^((6/5 : ℝ)*((k : ℝ)+1))/t^(k : ℝ))^(2 : ℕ)*K ≤ a/8 ∧
      ∀ m ≤ k/2, C m*(t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^m ≤ ρ*t := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  let M := 1 + ∑ m ∈ Finset.range (k/2+1), |C m|
  have hM : 0 < M := by
    have hh : 0 ≤ ∑ m ∈ Finset.range (k/2+1), |C m| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp [M]
    linarith
  have hCM (m : ℕ) (hm : m ≤ k/2) : C m ≤ M := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (k/2+1)) => abs_nonneg (C j))
      (Finset.mem_range.mpr (by omega : m < k/2+1))
    have hc := le_abs_self (C m)
    dsimp [M]
    linarith
  obtain ⟨ε₁,hε₁,hε₁1,h₁⟩ := positive_power_threshold 1 (1/10) η (by norm_num) hη
  obtain ⟨ε₂,hε₂,_,h₂⟩ := positive_power_threshold (D*B) (4*((k : ℝ)+1))
    (min (ρ/4) (a/8)) (by linarith) (lt_min (by positivity) (by positivity))
  obtain ⟨ε₃,hε₃,_,h₃⟩ := positive_power_threshold K ((2*(k : ℝ)+12)/5)
    (a/8) (by linarith) (by positivity)
  obtain ⟨ε₄,hε₄,_,h₄⟩ := positive_power_threshold M (1/10) ρ (by norm_num) hρ
  let ε := min ε₁ (min ε₂ (min ε₃ ε₄))
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ (lt_min hε₃ hε₄))
  have hε1 : ε ≤ ε₁ := min_le_left _ _
  have hε2 : ε ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ ε₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε4 : ε ≤ ε₄ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε,hε,hε1.trans hε₁1,?_⟩
  intro t ht hsmall
  have ht1 : t ≤ 1 := (hsmall.trans_le hε1).le.trans hε₁1
  have hr : t^(6/5 : ℝ)/t^(11/10 : ℝ) = t^(1/10 : ℝ) := by
    rw [← Real.rpow_sub ht]
    norm_num
  have hs : t^(11/10 : ℝ)/t = t^(1/10 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one t]
    rw [← Real.rpow_sub ht]
    norm_num
  have hpow : (t^(11/10 : ℝ)/t)^(40*(k+1)) = t^(4*((k : ℝ)+1)) := by
    rw [hs,← Real.rpow_natCast,← Real.rpow_mul ht.le]
    congr 1
    push_cast
    ring
  have hδ : (t^((6/5 : ℝ)*((k : ℝ)+1))/t^(k : ℝ))^(2 : ℕ) =
      t^((2*(k : ℝ)+12)/5) := by
    rw [← Real.rpow_sub ht,← Real.rpow_natCast,← Real.rpow_mul ht.le]
    congr 1
    ring
  refine ⟨?_,?_,?_,?_⟩
  · rw [hr]
    simpa only [one_mul] using (h₁ t ht (hsmall.trans_le hε1)).le
  · rw [hpow]
    exact (h₂ t ht (hsmall.trans_le hε2)).le
  · rw [hδ,mul_comm]
    exact (h₃ t ht (hsmall.trans_le hε3)).le
  · intro m hm
    let e : ℝ := (k : ℝ) + (1/5 : ℝ) - (6/5 : ℝ)*(m : ℝ)
    have hmk : 2*m ≤ k := by omega
    have hmk' : (2 : ℝ)*(m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have he : (1/10 : ℝ) ≤ e := by dsimp [e]; linarith
    have hratio : (t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^m = t^e*t := by
      rw [← Real.rpow_natCast,← Real.rpow_mul ht.le,scale_quotient_product ht]
      conv_rhs => rhs; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      dsimp [e]
      ring
    have hbound : C m*t^e ≤ ρ := by
      calc
        _ ≤ M*t^e := mul_le_mul_of_nonneg_right (hCM m hm) (Real.rpow_nonneg ht.le _)
        _ ≤ M*t^(1/10 : ℝ) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge ht ht1 he) hM.le
        _ ≤ ρ := (h₄ t ht (hsmall.trans_le hε4)).le
    calc
      _ = C m*((t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^m) := by ring
      _ = (C m*t^e)*t := by rw [hratio]; ring
      _ ≤ ρ*t := mul_le_mul_of_nonneg_right hbound ht.le

/-- One threshold allows either retaining the current order or increasing it
by one. The retained-order amplitude is the larger of the two possibilities. -/
theorem fixed_order_threshold_hold_advance (k : ℕ) (hk : 10 ≤ k)
    (ρ a η D B K : ℝ) (hρ : 0 < ρ) (ha : 0 < a) (hη : 0 < η)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hK : 0 ≤ K) (C : ℕ → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < ε →
      ∀ j : ℕ, k ≤ j → j ≤ k+1 →
      t^(6/5 : ℝ)/t^(11/10 : ℝ) ≤ η ∧
      D*B*(t^(11/10 : ℝ)/t)^(40*(k+1)) ≤ min (ρ/4) (a/8) ∧
      (t^((6/5 : ℝ)*(j : ℝ))/t^(k : ℝ))^(2 : ℕ)*K ≤ a/8 ∧
      (∀ m ≤ k/2, C m*(t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^m ≤ ρ*t) ∧
      t^((6/5 : ℝ)*(j : ℝ)) ≤ t^(k : ℝ) ∧
      t^((6/5 : ℝ)*((k : ℝ)+1)) ≤ t^((6/5 : ℝ)*(j : ℝ)) := by
  obtain ⟨ε₀,hε₀,hε₀1,hbase⟩ := fixed_order_threshold k hk ρ a η D B K
    hρ ha hη hD hB hK C
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨ε₁,hε₁,_,hhold⟩ := positive_power_threshold K ((2/5 : ℝ)*(k : ℝ))
    (a/8) (by linarith) (by positivity)
  refine ⟨min ε₀ ε₁,lt_min hε₀ hε₁,(min_le_left _ _).trans hε₀1,?_⟩
  intro t ht htε j hkj hjk
  have htε₀ : t < ε₀ := htε.trans_le (min_le_left _ _)
  have htε₁ : t < ε₁ := htε.trans_le (min_le_right _ _)
  have ht1 : t ≤ 1 := htε₀.le.trans hε₀1
  obtain ⟨hηt,htail,_,hderiv⟩ := hbase t ht htε₀
  have hkj' : (k : ℝ) ≤ j := by exact_mod_cast hkj
  have hjk' : (j : ℝ) ≤ (k : ℝ)+1 := by exact_mod_cast hjk
  have hamplitude : t^((6/5 : ℝ)*(j : ℝ)) ≤ t^((6/5 : ℝ)*(k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have hratio : t^((6/5 : ℝ)*(j : ℝ))/t^(k : ℝ) ≤
      t^((6/5 : ℝ)*(k : ℝ))/t^(k : ℝ) :=
    div_le_div_of_nonneg_right hamplitude (Real.rpow_nonneg ht.le _)
  have hholdpow : (t^((6/5 : ℝ)*(k : ℝ))/t^(k : ℝ))^(2 : ℕ) =
      t^((2/5 : ℝ)*(k : ℝ)) := by
    rw [← Real.rpow_sub ht,← Real.rpow_natCast,← Real.rpow_mul ht.le]
    congr 1
    ring
  refine ⟨hηt,htail,?_,hderiv,?_,?_⟩
  · calc
      _ ≤ (t^((6/5 : ℝ)*(k : ℝ))/t^(k : ℝ))^(2 : ℕ)*K :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀
          (div_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _)) hratio 2) hK
      _ = K*t^((2/5 : ℝ)*(k : ℝ)) := by rw [hholdpow,mul_comm]
      _ ≤ a/8 := (hhold t ht htε₁).le
  · exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
