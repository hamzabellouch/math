import OAI.Geometry.SurfaceImmersion.Correction.ExactCorrectionRecurrence
import OAI.Geometry.SurfaceImmersion.Correction.CorrectionBudgetThresholds

namespace OAI

/-! Scalar progress of an adaptive derivative order. No uniform control of
all the higher input norms is required. -/
noncomputable section
open Filter
open scoped Topology
namespace ClosedSurfaceR4.ExactCorrection

lemma eventually_lt_of_eventual_vanishing_recurrence
    {x c : ℕ → ℝ} {A L : ℝ} (hx : ∀ n, 0 ≤ x n) (hA : 0 ≤ A)
    (hc : Tendsto c atTop (𝓝 0))
    (hstep : ∀ᶠ n in atTop, x (n+1) ≤ A+c n*(1+x n)) (hAL : A < L) :
    ∀ᶠ n in atTop, x n < L := by
  let a : ℝ := (L-A)/(2*(L+1))
  have hL : 0 < L := lt_of_le_of_lt hA hAL
  have hden : 0 < 2*(L+1) := by positivity
  have ha : 0 < a := div_pos (sub_pos.mpr hAL) hden
  have ha1 : a < 1 := by
    dsimp [a]
    apply (div_lt_one hden).mpr
    linarith
  have hafix : (A+a)/(1-a) < L := by
    apply (div_lt_iff₀ (sub_pos.mpr ha1)).mpr
    have heq : a*(L+1) = (L-A)/2 := by dsimp [a]; field_simp
    nlinarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hstep.and (hc.eventually (gt_mem_nhds ha)))
  apply eventually_lt_of_affine_tail ha.le ha1 hafix N
  intro n hn
  have h1 := (hN n hn).1
  have h2 := mul_le_mul_of_nonneg_right (hN n hn).2.le (by linarith [hx n] : 0 ≤ 1+x n)
  nlinarith

lemma order_tendsto_of_no_constant_tail {k : ℕ → ℕ} (hmono : Monotone k)
    (hno : ∀ j N, ¬ ∀ n ≥ N, k n = j) : Tendsto k atTop atTop := by
  apply hmono.tendsto_atTop_atTop_iff.mpr
  intro m
  induction m with
  | zero => exact ⟨0,Nat.zero_le _⟩
  | succ m ih =>
    obtain ⟨N,hN⟩ := ih
    by_contra h
    push Not at h
    apply hno m N
    intro n hn
    have hupper := h n
    have hlower := hN.trans (hmono hn)
    omega

/-- Holding one order forever is impossible: every fixed higher input norm
contracts toward the baseline, so the rule must eventually advance. -/
theorem adaptive_order_tendsto
    {k : ℕ → ℕ} {x : ℕ → ℕ → ℝ} {t : ℕ → ℝ}
    {A B : ℝ} {N : ℕ → ℕ → ℝ} {ε : ℕ → ℝ} {r : ℕ → ℕ}
    (hA : 0 ≤ A) (hAB : A < B) (_hB : 0 < B)
    (hN : ∀ j m, 0 ≤ N j m) (hε : ∀ j, 0 < ε j)
    (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0))
    (hx : ∀ m n, 0 ≤ x m n)
    (hstep : ∀ m n, x m (n+1) ≤ A+N (k n) m*(t n)^(1/5 : ℝ)*(1+x m n))
    (hmono : Monotone k)
    (hadvance : ∀ n, t n < ε (k n+1) →
      A+N (k n) (r (k n+1))*(t n)^(1/5 : ℝ)*(1+x (r (k n+1)) n) ≤ B →
      k (n+1) = k n+1) : Tendsto k atTop atTop := by
  apply order_tendsto_of_no_constant_tail hmono
  intro j K hconstant
  have hpow : Tendsto (fun n => (t n)^(1/5 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1/5 : ℝ) ≠ 0)] using
      ht0.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1/5))
  have hc : Tendsto (fun n => N j (r (j+1))*(t n)^(1/5 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul (N j (r (j+1)))
  have hrec : ∀ᶠ n in atTop,
      x (r (j+1)) (n+1) ≤ A+N j (r (j+1))*(t n)^(1/5 : ℝ)*(1+x (r (j+1)) n) := by
    filter_upwards [eventually_ge_atTop K] with n hn
    simpa only [hconstant n hn] using hstep (r (j+1)) n
  have hxB := eventually_lt_of_eventual_vanishing_recurrence (hx (r (j+1))) hA hc hrec hAB
  obtain ⟨η,hη,_,hηbound⟩ := correction_budget_threshold
    (N := N j (r (j+1))) (L := (0 : ℝ)) hAB (by norm_num : (0 : ℝ) < 1)
  have hsmall := ht0.eventually (gt_mem_nhds (lt_min (hε (j+1)) hη))
  obtain ⟨n,hnK,hnB,hnt⟩ := (eventually_ge_atTop K |>.and (hxB.and hsmall)).exists
  have hkn := hconstant n hnK
  have hknext := hconstant (n+1) (by omega)
  have hb := (hηbound (t n) (ht n) (hnt.trans_le (min_le_right _ _))).1
  have hxle : x (r (j+1)) n ≤ B := hnB.le
  have hmul : N j (r (j+1))*(t n)^(1/5 : ℝ)*(1+x (r (j+1)) n) ≤
      N j (r (j+1))*(t n)^(1/5 : ℝ)*(1+B) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hxle)
      (mul_nonneg (hN j (r (j+1))) (Real.rpow_nonneg (ht n).le _))
  have hadv := hadvance n (by rw [hkn]; exact hnt.trans_le (min_le_left _ _))
    (by rw [hkn]; linarith)
  omega

end ClosedSurfaceR4.ExactCorrection

end

end OAI
