import OAI.Geometry.TranslativeCovering.BlockRow

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BlockDimension
open Finset BlockGeometry BlockCount BlockRow
variable {I : Type u_1} [Fintype I] [DecidableEq I]

lemma binary_cutoff {u : ℝ} (hu : 1 ≤ u) :
    let J := ⌈3*u/Real.log 2⌉₊
    (J:ℝ) ≤ (3/Real.log 2+1)*u ∧
      Real.exp (2*u)*(1/2:ℝ)^J ≤ 1 := by
  dsimp only
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnon : 0 ≤ 3*u/Real.log 2 := div_nonneg (by linarith) hl.le
  have hceil := (Nat.ceil_lt_add_one hnon).le
  have hlo := Nat.le_ceil (3*u/Real.log 2)
  constructor
  · simp only [div_eq_mul_inv] at hceil ⊢
    nlinarith
  · have he : (1/2:ℝ)^⌈3*u/Real.log 2⌉₊ =
        Real.exp (-((⌈3*u/Real.log 2⌉₊:ℕ):ℝ)*Real.log 2) := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
      simp [one_div]
    rw [he, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have hh := (div_le_iff₀ hl).mp hlo
    linarith

lemma uniform_row {L ζ C0 c0 q0 u : ℝ}
    (hL : 0 < L) (hζ : 0 < ζ) (hC0 : 1 ≤ C0) (hc0 : 0 < c0) (hq0 : 0 < q0)
    (hu : 1 ≤ u) (hcard : (Fintype.card I:ℝ) ≤ Real.exp (2*u))
    (d : I → I → ℝ) (hn : ∀ i j, 0 ≤ d i j) (hd : ∀ i, d i i = 0)
    (hs : ∀ i j, d i j = d j i) (htri : ∀ i j k, d i k ≤ d i j+d j k)
    (P : Finpartition (univ : Finset I))
    (hterm : ∀ H ⊆ P.parts, 2 ≤ H.card →
      ¬(radius d (H.biUnion id) ≤
          ((8*((Real.log C0+2)/c0)+16/L)*(2+3/Real.log 2))*u ∧
        loss L d (H.biUnion id) ≤ ζ*(H.biUnion id).card))
    (N0 : ℕ) (hN02 : 2 ≤ N0)
    (hlog : ∀ N : ℕ, N0 ≤ N → L*Real.log N ≤ ζ*N/2)
    (a : Finset I → I) (ha : ∀ T ∈ P.parts, a T ∈ T)
    (q : Finset I → ℝ) (hql : ∀ T ∈ P.parts, loss L d T ≤ q T)
    (S : Finset I) (hS : S ∈ P.parts) (hq : q0 ≤ q S)
    (w : Finset I → ℝ) (hw0 : ∀ T ∈ P.parts.erase S, 0 ≤ w T)
    (hw1 : ∀ T ∈ P.parts.erase S, w T ≤ 1)
    (hwt : ∀ T ∈ P.parts.erase S, w T ≤ Real.exp (-|q S-q T|/2))
    (hwa : ∀ T ∈ P.parts.erase S,
      w T ≤ C0*Real.exp ((loss L d S+loss L d T)/2-c0*d (a S) (a T)^2)) :
    let C := (N0:ℝ)+(2*L/ζ)*(1+8*((Real.log C0+2)/c0)+16/L)
    Real.log (1+∑ T ∈ P.parts.erase S,w T) ≤ max (2*C+(1+4*C)/q0) 3*q S := by
  dsimp only
  let C := (N0:ℝ)+(2*L/ζ)*(1+8*((Real.log C0+2)/c0)+16/L)
  have hqpos : 0 ≤ q S := hq0.le.trans hq
  have hct : ((P.parts.erase S).card:ℝ) ≤ Real.exp (2*u) := by
    apply le_trans _ hcard
    exact_mod_cast (card_erase_le.trans P.card_parts_le_card)
  by_cases hqu : q S ≤ u
  · let J := ⌈3*u/Real.log 2⌉₊
    obtain ⟨hJ,ht⟩ := binary_cutoff hu
    have htail : ((P.parts.erase S).card:ℝ)*(1/2:ℝ)^J ≤ 1 :=
      (mul_le_mul_of_nonneg_right hct (by positivity)).trans ht
    have hcut (k : ℕ) (hk : k < J) :
        (8*((Real.log C0+2)/c0)+16/L)*(q S+k+1) ≤
          ((8*((Real.log C0+2)/c0)+16/L)*(2+3/Real.log 2))*u := by
      have hk' : (k:ℝ)+1 ≤ J := by exact_mod_cast hk
      have ha : 0 ≤ (Real.log C0+2)/c0 := div_nonneg (by linarith [Real.log_nonneg hC0]) hc0.le
      have hf : 0 ≤ 8*((Real.log C0+2)/c0)+16/L := by positivity
      have hbase : q S+k+1 ≤ (2+3/Real.log 2)*u := by dsimp [J] at hk'; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hbase hf]
    have hrow := logarithmic_row hL hζ hC0 hc0 hq0 d hn hd hs htri P hterm
      N0 hN02 hlog a ha q hql S hS hq w hw0 hw1 hwt hwa J htail hcut
    exact hrow.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hqpos)
  · have hsum : ∑ T ∈ P.parts.erase S,w T ≤ Real.exp (2*u) := by
      calc _ ≤ ∑ _T ∈ P.parts.erase S,(1:ℝ) := sum_le_sum hw1
           _ = ((P.parts.erase S).card:ℝ) := by simp
           _ ≤ _ := hct
    have h2 : Real.log 2 ≤ u := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith
    have hExp : 1+Real.exp (2*u) ≤ Real.exp (3*u) := by
      have h1 : 1 ≤ Real.exp (2*u) := Real.one_le_exp_iff.mpr (by linarith)
      have h2' : 2 ≤ Real.exp u := by simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr h2
      have he : Real.exp (3*u) = Real.exp (2*u)*Real.exp u := by rw [← Real.exp_add]; congr 1; ring
      rw [he]
      nlinarith [Real.exp_pos (2*u)]
    have hleftpos : 0 < 1+∑ T ∈ P.parts.erase S,w T := by
      have := sum_nonneg hw0
      linarith
    have hbd : Real.log (1+∑ T ∈ P.parts.erase S,w T) ≤ 3*u := by
      have hp := Real.log_le_log hleftpos (show 1+∑ T ∈ P.parts.erase S,w T ≤ Real.exp (3*u) by linarith)
      simpa only [Real.log_exp] using hp
    exact hbd.trans ((by nlinarith : 3*u ≤ 3*q S).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hqpos))

end BlockDimension

end OAI
