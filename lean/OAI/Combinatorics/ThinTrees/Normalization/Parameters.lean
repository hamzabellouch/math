import Mathlib
import OAI.Combinatorics.ThinTrees.Normalization.Algorithm

namespace OAI

/-! Normalization parameters. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder

lemma multiplier_bounds (r : ℕ) (hr : 1 ≤ r) :
    0 < multiplier r ∧ multiplier r < 1 ∧
    0 < decrement (multiplier r) ∧ decrement (multiplier r) ≤ 1/2 ∧
    1/(16*(r:ℚ)^2) ≤ decrement (multiplier r) ∧
    decrement (multiplier r) ≤ 1/(8*(r:ℚ)^2) := by
  have hr1 : (1:ℚ) ≤ r := by exact_mod_cast hr
  have hr2 : (1:ℚ) ≤ (r:ℚ)^2 := one_le_pow₀ hr1
  have hd : (0:ℚ) < 16*(r:ℚ)^2 := by positivity
  have hx : (0:ℚ) < 1/(16*(r:ℚ)^2) := div_pos zero_lt_one hd
  have hx1 : (1:ℚ)/(16*(r:ℚ)^2) ≤ 1/16 := by
    rw [div_le_div_iff₀ hd (by norm_num : (0:ℚ)<16)]
    linarith only [hr2]
  have he : 1/(8*(r:ℚ)^2)=2*(1/(16*(r:ℚ)^2)) := by ring
  unfold multiplier decrement
  rw [he]
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg (1/(16*(r:ℚ)^2))]

lemma normalizationLength_suffices (m r : ℕ) (hr : 1 ≤ r) :
    2*(m:ℝ) < (normalizationLength m r:ℝ)*(decrement (multiplier r):ℝ)^2 := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hδ := (multiplier_bounds r hr).2.2.2.2.1
  have hδR : 1/(16*(r:ℝ)^2) ≤ (decrement (multiplier r):ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hδ
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,
      Rat.cast_natCast,Rat.cast_one] using hh
  have hsq := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/(16*(r:ℝ)^2)) hδR 2
  have hN : (normalizationLength m r:ℝ)=(2*(m:ℝ)+1)*256*(r:ℝ)^4 := by
    simp only [normalizationLength,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,Nat.cast_pow]
  have he : (normalizationLength m r:ℝ)*(1/(16*(r:ℝ)^2))^2=2*(m:ℝ)+1 := by
    rw [hN]
    field_simp [ne_of_gt hr0]
    ring
  have hh := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (normalizationLength m r) : (0:ℝ) ≤ _)
  rw [he] at hh
  linarith only [hh]

lemma threshold_le (q r : ℕ) (hq : 0 < q) (hqr : q ≤ r) :
    (threshold q (multiplier r):ℝ) ≤ (1+4/(r:ℝ))/(q:ℝ) := by
  have hr : 1 ≤ r := Nat.le_trans hq hqr
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hqrR : (q:ℝ) ≤ r := by exact_mod_cast hqr
  have hδ := (multiplier_bounds r hr).2.2.2.2.2
  have hδR : (decrement (multiplier r):ℝ) ≤ 1/(8*(r:ℝ)^2) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hδ
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,
      Rat.cast_natCast,Rat.cast_one] using hh
  have hh : 4*(decrement (multiplier r):ℝ) ≤ 4/((r:ℝ)*q) := by
    apply (mul_le_mul_of_nonneg_left hδR (by norm_num : (0:ℝ) ≤ 4)).trans
    have hc : (r:ℝ)*q ≤ 8*(r:ℝ)^2 := by nlinarith only [mul_le_mul_of_nonneg_left hqrR hrR.le,sq_nonneg (r:ℝ)]
    have hi := one_div_le_one_div_of_le (mul_pos hrR hqR) hc
    calc
      4*(1/(8*(r:ℝ)^2)) ≤ 4*(1/((r:ℝ)*q)) := mul_le_mul_of_nonneg_left hi (by norm_num)
      _ = _ := by ring
  simp only [threshold,Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,
    Rat.cast_mul,Rat.cast_ofNat]
  have he : (1+4/(r:ℝ))/(q:ℝ)=1/(q:ℝ)+4/((r:ℝ)*q) := by ring
  rw [he]
  linarith only [hh]

lemma multiplier_parts (r : ℕ) :
    CurrentKS.RationalBits.Parts (5+2*r.size) (multiplier r) := by
  have hr := CurrentKS.RationalBits.natCast_parts r
  have h16 : CurrentKS.RationalBits.Parts 4 (16:ℚ) := by norm_num [CurrentKS.RationalBits.Parts]
  have hh := CurrentKS.RationalBits.parts_one.add ((h16.mul (hr.mul hr)).inv.neg)
  convert hh using 1
  · omega
  · simp only [multiplier,sub_eq_add_neg,one_div,pow_two]

theorem normalizedScales_correct {m d q r : ℕ} (v : Fin m → Fin d → ℚ)
    (B : ContainedPacking (realColumns v) q) (hqr : q ≤ r)
    (hsize : ∀e, realColumns v e ⬝ᵥ realColumns v e ≤ 2) :
    let s := normalizedScales q r v
    (∀e, 0 < s e ∧ s e ≤ 1) ∧
    (∀e, leverage (realColumns v) (realWeights s) e ≤ (1+4/(r:ℝ))/(q:ℝ)) ∧
    (∀e, CurrentKS.RationalBits.Parts (normalizationLength m r*(5+2*r.size)) (s e)) := by
  have hr : 1 ≤ r := B.positive.trans_le hqr
  obtain ⟨ht,ht1,hδ,hδ1,hδlower,hδupper⟩ := multiplier_bounds r hr
  have hbox := scalesAt_box q ht ht1.le v (normalizationLength m r)
  have hA := B.covariance_posDef _ (realWeights_box hbox).1
  have hq0 : (0:ℚ) < q := by exact_mod_cast B.positive
  have hth : 0 < threshold q (multiplier r) := by unfold threshold; positivity
  have hN := scalesAt_terminates q ht ht1 hδ hδ1 v B hsize
    (normalizationLength m r) (normalizationLength_suffices m r hr)
  refine ⟨hbox,?_,scalesAt_parts q _ v (multiplier_parts r) _⟩
  intro e
  exact (((heavy_none q (multiplier r) v _ (fun e => (hbox e).1) hA hth).mp hN) e).trans
    (threshold_le q r B.positive hqr)

end AlgorithmicThinTrees.Normalization
end

end OAI
