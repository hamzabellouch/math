import OAI.Combinatorics.EditApproximation.Geometry.BandEnvelopeBits
import OAI.Combinatorics.EditApproximation.Geometry.ChildIncrements

namespace OAI

/-! The actual finite optimistic-history sum has polynomial encoding
length. Its normalized table entries are bounded by the fixed envelopes. -/

namespace EditApproximation

open Finset

def onlineSummandEncodingBudget (tableBits massBits kappaBits : ℕ) : ℕ :=
  10 * tableBits + 4 * massBits + 4 * kappaBits + 56

def onlineLinearEncodingBudget (etaBits kappaBits massBits tableBits t : ℕ) : ℕ :=
  etaBits + 2 * (Nat.size (t * 2) +
    2 * (t * onlineSummandEncodingBudget tableBits massBits kappaBits + 1) + 1) +
    2 * (tableBits + massBits + 3) + 3

theorem childGain_encoding {β σ : Type*} (mass : β → ℚ) (table : ℕ → β × σ → ℚ)
    (s : ℕ) (i : β × σ) (Bm Bt : ℕ)
    (hm : rationalEncodingBits (mass i.1) ≤ Bm) (ht : rationalEncodingBits (table s i) ≤ Bt) :
    rationalEncodingBits (childGain mass table s i) ≤ Bt + Bm + 3 := by
  have h := rationalEncodingBits_div (-table s i) (mass i.1)
  rw [rationalEncodingBits_neg] at h
  exact h.trans (by omega)

theorem childDecrement_encoding {β σ : Type*} (mass : β → ℚ) (table : ℕ → β × σ → ℚ)
    (s : ℕ) (i : β × σ) (Bm Bt : ℕ)
    (hm : rationalEncodingBits (mass i.1) ≤ Bm)
    (ht : rationalEncodingBits (table s i) ≤ Bt)
    (ht' : rationalEncodingBits (table (s + 1) i) ≤ Bt) :
    rationalEncodingBits (childDecrement mass table s i) ≤ 4 * Bt + Bm + 5 := by
  have hs := rationalEncodingBits_sub (table s i) (table (s + 1) i)
  have hd := rationalEncodingBits_div (table s i - table (s + 1) i) (mass i.1)
  change rationalEncodingBits ((table s i - table (s + 1) i) / mass i.1) ≤ _
  omega

theorem childGain_abs_le_one {β σ : Type*} (mass : β → ℚ) (table : ℕ → β × σ → ℚ)
    (s : ℕ) (i : β × σ) (hm : 0 < mass i.1)
    (ht : 0 ≤ table s i ∧ table s i ≤ mass i.1) : |childGain mass table s i| ≤ 1 := by
  rw [childGain, abs_div, abs_neg, abs_of_nonneg ht.1, abs_of_pos hm]
  exact (div_le_one₀ hm).mpr ht.2

theorem childDecrement_abs_le_one {β σ : Type*} (mass : β → ℚ) (table : ℕ → β × σ → ℚ)
    (s : ℕ) (i : β × σ) (hm : 0 < mass i.1)
    (ht : 0 ≤ table s i ∧ table s i ≤ mass i.1)
    (ht' : 0 ≤ table (s + 1) i ∧ table (s + 1) i ≤ mass i.1) :
    |childDecrement mass table s i| ≤ 1 := by
  rw [childDecrement, abs_div, abs_of_pos hm]
  apply (div_le_one₀ hm).mpr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rationalOnlineLinear_encoding {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (eta kappa : ℚ) (t : ℕ) (i : β × σ)
    (Be Bk Bm Bt : ℕ) (heta : rationalEncodingBits eta ≤ Be)
    (hkappa : rationalEncodingBits kappa ≤ Bk)
    (hmass : rationalEncodingBits (mass i.1) ≤ Bm)
    (htable : ∀ s ≤ t + 1, rationalEncodingBits (table s i) ≤ Bt)
    (hmassPos : 0 < mass i.1) (hkappaRange : 0 ≤ kappa ∧ kappa ≤ 1)
    (htableRange : ∀ s ≤ t + 1, 0 ≤ table s i ∧ table s i ≤ mass i.1) :
    rationalEncodingBits (rationalOnlineLinear eta kappa (childGain mass table)
      (childDecrement mass table) t i) ≤ onlineLinearEncodingBudget Be Bk Bm Bt t := by
  let term := fun s => childGain mass table s i + (1 - 2 * kappa) * childDecrement mass table s i
  have htwo : rationalEncodingBits (2 : ℚ) = 4 := by
    rw [show (2 : ℚ) = (2 : ℕ) by norm_num, rationalEncodingBits_natCast]
    rfl
  have hone : rationalEncodingBits (1 : ℚ) = 3 := by norm_num [rationalEncodingBits]
  have hcoeff : rationalEncodingBits (1 - 2 * kappa) ≤ 2 * Bk + 18 := by
    have hm := rationalEncodingBits_mul 2 kappa
    have hs := rationalEncodingBits_sub 1 (2 * kappa)
    rw [htwo] at hm
    rw [hone] at hs
    omega
  have hcoeffAbs : |1 - 2 * kappa| ≤ 1 := abs_le.mpr ⟨by linarith [hkappaRange.1, hkappaRange.2], by linarith [hkappaRange.1]⟩
  have hterm (s : ℕ) (hs : s < t) : rationalEncodingBits (term s) ≤ onlineSummandEncodingBudget Bt Bm Bk := by
    have hg := childGain_encoding mass table s i Bm Bt hmass (htable s (by omega))
    have hd := childDecrement_encoding mass table s i Bm Bt hmass (htable s (by omega)) (htable (s + 1) (by omega))
    have hp := rationalEncodingBits_mul (1 - 2 * kappa) (childDecrement mass table s i)
    have ha := rationalEncodingBits_add (childGain mass table s i) ((1 - 2 * kappa) * childDecrement mass table s i)
    change rationalEncodingBits (childGain mass table s i + (1 - 2 * kappa) * childDecrement mass table s i) ≤ _
    unfold onlineSummandEncodingBudget
    omega
  have htermAbs (s : ℕ) (hs : s < t) : |term s| ≤ 2 := by
    have hg := childGain_abs_le_one mass table s i hmassPos (htableRange s (by omega))
    have hd := childDecrement_abs_le_one mass table s i hmassPos (htableRange s (by omega)) (htableRange (s + 1) (by omega))
    have hp := mul_le_mul hcoeffAbs hd (abs_nonneg _) (by norm_num : (0 : ℚ) ≤ 1)
    have ha := abs_add_le (childGain mass table s i) ((1 - 2 * kappa) * childDecrement mass table s i)
    rw [abs_mul] at ha
    dsimp only [term]
    linarith
  have hsum := rational_finite_sum_encoding_le (range t) term 2 (onlineSummandEncodingBudget Bt Bm Bk)
    (fun s hs => htermAbs s (mem_range.mp hs)) (by
      intro s hs
      have h := hterm s (mem_range.mp hs)
      unfold rationalEncodingBits at h
      omega)
  simp only [card_range] at hsum
  have hg := childGain_encoding mass table t i Bm Bt hmass (htable t (by omega))
  have ha := rationalEncodingBits_add (∑ s ∈ range t, term s) (childGain mass table t i)
  have hm := rationalEncodingBits_mul eta ((∑ s ∈ range t, term s) + childGain mass table t i)
  change rationalEncodingBits (eta * ((∑ s ∈ range t, term s) + childGain mass table t i)) ≤ _
  unfold onlineLinearEncodingBudget
  omega

theorem rationalOnlineLinear_abs {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (eta kappa : ℚ) (t E : ℕ) (i : β × σ)
    (heta : |eta| ≤ E) (hmass : 0 < mass i.1) (hkappa : 0 ≤ kappa ∧ kappa ≤ 1)
    (htable : ∀ s ≤ t + 1, 0 ≤ table s i ∧ table s i ≤ mass i.1) :
    |rationalOnlineLinear eta kappa (childGain mass table) (childDecrement mass table) t i| ≤ E * (2 * t + 1) := by
  have hc : |1 - 2 * kappa| ≤ 1 := abs_le.mpr ⟨by linarith [hkappa.2], by linarith [hkappa.1]⟩
  have hterm (s : ℕ) (hs : s ∈ range t) :
      |childGain mass table s i + (1 - 2 * kappa) * childDecrement mass table s i| ≤ 2 := by
    have hs' := mem_range.mp hs
    have hg := childGain_abs_le_one mass table s i hmass (htable s (by omega))
    have hd := childDecrement_abs_le_one mass table s i hmass (htable s (by omega)) (htable (s + 1) (by omega))
    have hp := mul_le_mul hc hd (abs_nonneg _) (by norm_num : (0 : ℚ) ≤ 1)
    exact (abs_add_le _ _).trans (by rw [abs_mul]; linarith)
  have hsum : |rationalOptimisticHistory kappa (childGain mass table) (childDecrement mass table) t i| ≤ 2 * t := by
    unfold rationalOptimisticHistory
    calc
      _ ≤ ∑ s ∈ range t, |childGain mass table s i + (1 - 2 * kappa) * childDecrement mass table s i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ range t, (2 : ℚ) := sum_le_sum hterm
      _ = _ := by simp; ring
  have hg := childGain_abs_le_one mass table t i hmass (htable t (by omega))
  unfold rationalOnlineLinear
  rw [abs_mul]
  exact mul_le_mul heta ((abs_add_le _ _).trans (add_le_add hsum hg)) (abs_nonneg _) (Nat.cast_nonneg _)

end EditApproximation

end OAI
