import OAI.NumberTheory.TotientAsymptotic.LocalSquareCutoff

namespace OAI

/-! The concrete square cutoff saves every fixed power of the local double logarithm. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma local_square_error_decay {C : ℝ} (hC : 0 < C) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,C*(B z+2)/(Real.log z)^3 ≤ (B z)^(-K) := by
  have ht : Tendsto (fun t : ℝ => (3*C)*t^(K+1)*Real.exp (-3*t)) atTop (nhds 0) := by
    simpa only [mul_zero,mul_assoc] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (K+1) 3 (by norm_num)).const_mul (3*C)
  filter_upwards [B_tendsto.eventually (ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))),
    B_tendsto.eventually (eventually_ge_atTop (1:ℝ)),eventually_gt_atTop (1:ℝ)]
    with z hz hB hz1
  have hB0 : 0 < B z := zero_lt_one.trans_le hB
  have hl : 0 < Real.log z := Real.log_pos hz1
  have he : Real.exp (-3*B z)=((Real.log z)^3)⁻¹ := by
    rw [show -3*B z= -((3:ℝ)*B z) by ring,Real.exp_neg]
    have hh : Real.exp ((3:ℝ)*B z)=(Real.log z)^3 := by
      simpa only [Nat.cast_ofNat,B,Real.exp_log hl] using Real.exp_nat_mul (B z) 3
    rw [hh]
  have hpower : (B z)^(K+1)=(B z)^K*B z := by
    rw [Real.rpow_add hB0,Real.rpow_one]
  have hmain : (C*(B z+2)/(Real.log z)^3)*(B z)^K ≤ 1 := by
    have hle : C*(B z+2) ≤ (3*C)*B z := by nlinarith only [hC,hB]
    have hh := mul_le_mul_of_nonneg_right hle
      (mul_nonneg (inv_pos.mpr (pow_pos hl 3)).le (Real.rpow_pos_of_pos hB0 K).le)
    calc
      _ = C*(B z+2)*(((Real.log z)^3)⁻¹*(B z)^K) := by ring
      _ ≤ (3*C)*B z*(((Real.log z)^3)⁻¹*(B z)^K) := hh
      _ ≤ 1 := by
        rw [hpower,he] at hz
        convert hz.le using 1
        ring
  have hpos := Real.rpow_pos_of_pos hB0 K
  have hh := (le_div_iff₀ hpos).mpr hmain
  simpa only [one_div,Real.rpow_neg hB0.le] using hh

theorem local_square_witness_power_saving (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,∀ (S : Finset ℕ) (F : ℕ → ℕ),Set.InjOn F (S : Set ℕ) →
      (∀ n ∈ S,0 < F n ∧ ((F n).totient:ℝ) ≤ z) →
      (∀ n ∈ S,∃ p : ℕ,p.Prime ∧ localSquareCutoff z<p ∧
        (p^2 ∣ F n ∨ p^2 ∣ (F n).totient)) →
      (S.card:ℝ) ≤ z/Real.log z*(B z)^(-K) := by
  obtain ⟨C,hC,hcount⟩ := local_square_witness_count
  filter_upwards [hcount,local_square_error_decay hC K,eventually_gt_atTop (1:ℝ)] with z hz hdec hz1
  intro S F hinj hF hsq
  have hfac : 0 ≤ z/Real.log z := (div_pos (zero_lt_one.trans hz1) (Real.log_pos hz1)).le
  calc
    _ ≤ C*z*(B z+2)/(Real.log z)^4 := hz S F hinj hF hsq
    _ = (z/Real.log z)*(C*(B z+2)/(Real.log z)^3) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hdec hfac

end TotientAsymptotic

end

end OAI
