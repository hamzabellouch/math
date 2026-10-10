import OAI.NumberTheory.TotientAsymptotic.PPTIndexGap

namespace OAI

/-!
A vacant terminal window is chosen from the actual finite list of left
prime heights. Its width remains larger than the local normality error,
so the comparison's last upper cutoff can be placed inside that window.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- Among `n+1` disjoint closed windows, one misses all `n` coordinates. -/
lemma ppt_empty_separated_window {n : ℕ} (x : Fin n → ℝ) {T δ : ℝ}
    (hδ : 0 < δ) :
    ∃ j : Fin (n+1), ∀ i : Fin n,
      ¬(T+2*(j.val : ℝ)*δ ≤ x i ∧ x i ≤ T+(2*(j.val : ℝ)+1)*δ) := by
  classical
  by_contra hnone
  push Not at hnone
  choose f hf using hnone
  have hsep {j k : Fin (n+1)} (hjk : j < k) :
      T+(2*(j.val : ℝ)+1)*δ < T+2*(k.val : ℝ)*δ := by
    have hc : (j.val : ℝ)+1 ≤ k.val := by
      exact_mod_cast (Nat.succ_le_of_lt hjk)
    nlinarith only [hc, hδ]
  have hinj : Function.Injective f := by
    intro j k heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hjk | hkj
    · have hh := hsep hjk
      have hj := (hf j).2
      have hk := (hf k).1
      rw [heq] at hj
      linarith only [hh, hj, hk]
    · have hh := hsep hkj
      have hj := (hf j).1
      have hk := (hf k).2
      rw [heq] at hj
      linarith only [hh, hj, hk]
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hc
  omega

/-- An empty height window splits a decreasing list into a high prefix
and a low suffix; equality at either endpoint is excluded. -/
lemma ppt_antitone_split_at_empty_window {n : ℕ} (x : Fin n → ℝ)
    (hx : Antitone x) {L U : ℝ}
    (hempty : ∀ i, ¬(L ≤ x i ∧ x i ≤ U)) :
    ∃ J : ℕ, J ≤ n ∧
      (∀ i : Fin n, i.val < J → U < x i) ∧
      (∀ i : Fin n, J ≤ i.val → x i < L) := by
  classical
  by_cases hex : ∃ j : ℕ, ∃ hj : j < n, x ⟨j,hj⟩ ≤ U
  · obtain ⟨hJn, hJU⟩ := Nat.find_spec hex
    have hJL : x ⟨Nat.find hex,hJn⟩ < L := by
      by_contra hn
      exact hempty _ ⟨le_of_not_gt hn, hJU⟩
    refine ⟨Nat.find hex, hJn.le, ?_, ?_⟩
    · intro i hi
      by_contra hn
      exact Nat.find_min hex hi ⟨i.isLt, le_of_not_gt hn⟩
    · intro i hi
      exact (hx (show (⟨Nat.find hex,hJn⟩ : Fin n) ≤ i from hi)).trans_lt hJL
  · refine ⟨n, le_rfl, ?_, ?_⟩
    · intro i hi
      by_contra hn
      exact hex ⟨i.val, i.isLt, le_of_not_gt hn⟩
    · intro i hi
      omega

/-- The terminal split has an explicit width even when the number of
left primes is smaller than the ambient dimension bound. -/
theorem ppt_terminal_gap {n H : ℕ} (x : Fin n → ℝ) (hx : Antitone x)
    {T : ℝ} (hT : 0 < T) (hn : n ≤ H) :
    ∃ L U : ℝ, ∃ J : ℕ,
      T ≤ L ∧ U ≤ 2*T ∧ L < U ∧
      T/(2*((H : ℝ)+1)) ≤ U-L ∧ J ≤ n ∧
      (∀ i : Fin n, i.val < J → U < x i) ∧
      (∀ i : Fin n, J ≤ i.val → x i < L) := by
  let δ : ℝ := T/(2*((n : ℝ)+1))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : 0 < 2*((n : ℝ)+1) := by positivity
  have hδ : 0 < δ := div_pos hT hden
  obtain ⟨j, hj⟩ := ppt_empty_separated_window x hδ
  let L : ℝ := T+2*(j.val : ℝ)*δ
  let U : ℝ := T+(2*(j.val : ℝ)+1)*δ
  obtain ⟨J, hJn, hhigh, hlow⟩ := ppt_antitone_split_at_empty_window x hx hj
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hjn : (j.val : ℝ) ≤ n := by
    exact_mod_cast (Nat.lt_succ_iff.mp j.isLt)
  have hδscale : (2*((n : ℝ)+1))*δ = T := by
    dsimp only [δ]
    field_simp
  have hwidth : U-L = δ := by dsimp only [U, L]; ring
  refine ⟨L, U, J, ?_, ?_, ?_, ?_, hJn, hhigh, hlow⟩
  · dsimp only [L]
    have hh : 0 ≤ 2*(j.val : ℝ)*δ := by positivity
    linarith only [hh]
  · dsimp only [U]
    nlinarith only [hδscale, hjn, hδ]
  · rw [← sub_pos, hwidth]
    exact hδ
  · rw [hwidth]
    exact div_le_div_of_nonneg_left hT.le hden (by exact_mod_cast
      (show 2*(n+1) ≤ 2*(H+1) by omega))

/-- Normality errors fit inside a reciprocal-dimension fraction of the
terminal height range. This is stronger than a fixed-fraction gap. -/
theorem ppt_terminal_normality_budget {A η : ℝ} (_hA : 0 < A) (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop, ∀ (H J : ℕ) (s X : ℝ),
      1 ≤ H → J ≤ H → (H : ℝ) ≤ A*Real.log t →
      0 ≤ s → s ≤ (H : ℝ)^4 → 0 ≤ X → X ≤ t →
      (2*(J : ℝ)+1)*Real.sqrt (s*X)+s < η*t^(2/3 : ℝ)/((H : ℝ)+1) := by
  have h₄ : Tendsto (fun t : ℝ => (Real.log t)^4/t^(1/6 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (4 : ℕ)
        (by norm_num : (0 : ℝ) < 1/6)).tendsto_div_nhds_zero
  have h₅ : Tendsto (fun t : ℝ => (Real.log t)^5/t^(2/3 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (5 : ℕ)
        (by norm_num : (0 : ℝ) < 2/3)).tendsto_div_nhds_zero
  have hsum : Tendsto (fun t : ℝ =>
      6*A^4*((Real.log t)^4/t^(1/6 : ℝ))+2*A^5*((Real.log t)^5/t^(2/3 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (h₄.const_mul (6*A^4)).add (h₅.const_mul (2*A^5))
  filter_upwards [hsum.eventually (eventually_lt_nhds hη),
    eventually_gt_atTop (0 : ℝ)] with t hbudget ht
  intro H J s X hH hJ hdim hs0 hs hX0 hX
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hJr : (J : ℝ) ≤ H := by exact_mod_cast hJ
  have ht23 : 0 < t^(2/3 : ℝ) := Real.rpow_pos_of_pos ht _
  have hsqrt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hroot : Real.sqrt (s*X) ≤ (H : ℝ)^2*Real.sqrt t := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      s*X ≤ (H : ℝ)^4*t := mul_le_mul hs hX hX0 (by positivity)
      _ = ((H : ℝ)^2*Real.sqrt t)^2 := by
        rw [mul_pow, Real.sq_sqrt ht.le]
        ring
  have hleft : (2*(J : ℝ)+1)*Real.sqrt (s*X)+s ≤
      3*(H : ℝ)^3*Real.sqrt t+(H : ℝ)^4 := by
    have hmul := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ 2*(J : ℝ)+1 by positivity)
    have hcoef := mul_le_mul_of_nonneg_right
      (show 2*(J : ℝ)+1 ≤ 3*(H : ℝ) by linarith only [hJr, hHr])
      (show 0 ≤ (H : ℝ)^2*Real.sqrt t by positivity)
    nlinarith only [hmul, hcoef, hs]
  have hweighted :
      ((2*(J : ℝ)+1)*Real.sqrt (s*X)+s)*((H : ℝ)+1) ≤
        6*(H : ℝ)^4*Real.sqrt t+2*(H : ℝ)^5 := by
    have hmul := mul_le_mul_of_nonneg_right hleft
      (show 0 ≤ (H : ℝ)+1 by positivity)
    have hcoef := mul_le_mul_of_nonneg_left
      (show (H : ℝ)+1 ≤ 2*(H : ℝ) by linarith only [hHr])
      (show 0 ≤ 3*(H : ℝ)^3*Real.sqrt t+(H : ℝ)^4 by positivity)
    nlinarith only [hmul, hcoef]
  have hH4 := pow_le_pow_left₀ hH0 hdim 4
  have hH5 := pow_le_pow_left₀ hH0 hdim 5
  have hscale : 6*(H : ℝ)^4*Real.sqrt t+2*(H : ℝ)^5 ≤
      6*(A*Real.log t)^4*Real.sqrt t+2*(A*Real.log t)^5 := by
    exact add_le_add (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hH4 (by norm_num)) hsqrt)
      (mul_le_mul_of_nonneg_left hH5 (by norm_num))
  have hratio : Real.sqrt t/t^(2/3 : ℝ) = 1/t^(1/6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub ht,
      show (1/2 : ℝ)-(2/3 : ℝ) = -(1/6 : ℝ) by norm_num,
      Real.rpow_neg ht.le]
    simp only [one_div]
  have he : (6*(A*Real.log t)^4*Real.sqrt t+2*(A*Real.log t)^5)/t^(2/3 : ℝ) =
      6*A^4*((Real.log t)^4/t^(1/6 : ℝ))+2*A^5*((Real.log t)^5/t^(2/3 : ℝ)) := by
    rw [add_div, mul_div_assoc, hratio]
    ring
  have htop : 6*(A*Real.log t)^4*Real.sqrt t+2*(A*Real.log t)^5 < η*t^(2/3 : ℝ) := by
    apply (div_lt_iff₀ ht23).mp
    rwa [he]
  apply (lt_div_iff₀ (show 0 < (H : ℝ)+1 by positivity)).mpr
  exact hweighted.trans_lt (hscale.trans_lt htop)

end TotientAsymptotic

end

end OAI
