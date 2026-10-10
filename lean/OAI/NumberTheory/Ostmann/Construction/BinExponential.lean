import OAI.NumberTheory.Ostmann.Conclusion.Scales
import OAI.NumberTheory.Ostmann.Construction.GiantWindowScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter

lemma exp_neg_nat_le_half_pow (b : ℕ) : Real.exp (-(b:ℝ)) ≤ (1/2:ℝ)^b := by
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hi : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0:ℝ)<2)).mpr he
  have hp := pow_le_pow_left₀ (Real.exp_pos (-1)).le hi b
  have heq : Real.exp (-(b:ℝ))=Real.exp (-1)^b := by
    simpa only [mul_neg, mul_one] using Real.exp_nat_mul (-1) b
  rwa [heq]

theorem bin_denominator_eventually {k : ℕ} (hk : 0<k) {β : ℝ} (hβ : β<1) :
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, b ≤ Conclusion.bulkSize k L →
      2*((b:ℝ)*Real.exp (β*L)+5) ≤ Real.exp (2*(Conclusion.bulkSize k L:ℝ)) := by
  have hz : 1 ≤ Conclusion.bulkScale k := by
    unfold Conclusion.bulkScale
    apply one_le_pow₀
    exact_mod_cast (show 1 ≤ k by omega)
  have hrate : ∀ᶠ L : ℝ in atTop,
      4*Conclusion.bulkScale k*Real.exp 4 ≤ Real.exp ((1-β)*L)/L := by
    simpa only [Real.rpow_one] using
      (tendsto_exp_mul_div_rpow_atTop 1 (1-β) (by linarith)).eventually_ge_atTop
        (4*Conclusion.bulkScale k*Real.exp 4)
  have hexp := (exp_mul_tendsto (by norm_num : (0:ℝ)<1)).eventually_ge_atTop (20*Real.exp 4)
  filter_upwards [hrate,hexp,eventually_ge_atTop (1:ℝ)] with L hr he hL
  intro b hb
  have hL0 : 0<L := by linarith
  have hm := Conclusion.bulkSize_bounds k hL0.le
  have hml : L-2 < (Conclusion.bulkSize k L:ℝ) := by nlinarith
  have hb' : (b:ℝ) ≤ Conclusion.bulkSize k L := by exact_mod_cast hb
  have hr' := (le_div_iff₀ hL0).mp hr
  have hr'' := mul_le_mul_of_nonneg_right hr' (Real.exp_pos (β*L)).le
  rw [← Real.exp_add, show (1-β)*L+β*L=L by ring] at hr''
  have hlo : Real.exp (2*L-4) ≤ Real.exp (2*(Conclusion.bulkSize k L:ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hex : Real.exp (2*L-4)=Real.exp L*Real.exp L/Real.exp 4 := by
    rw [Real.exp_sub,show 2*L=L+L by ring,Real.exp_add]
  have hge : 1 ≤ Real.exp L := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hL0.le
  have hbig : 2*((b:ℝ)*Real.exp (β*L)+5)*Real.exp 4 ≤ Real.exp L := by
    have hbb := mul_le_mul_of_nonneg_right (hb'.trans hm.2) (Real.exp_pos (β*L)).le
    have hbpos := (Real.exp_pos (β*L)).le
    simp only [one_mul] at he
    nlinarith [Real.exp_pos (4:ℝ)]
  calc
    _ ≤ Real.exp L/Real.exp 4 := (le_div_iff₀ (Real.exp_pos _)).mpr hbig
    _ ≤ Real.exp L*Real.exp L/Real.exp 4 :=
      div_le_div_of_nonneg_right (by nlinarith [Real.exp_pos L]) (Real.exp_pos _).le
    _ ≤ _ := by rw [← hex]; exact hlo

theorem bin_weight_lower_eventually {k : ℕ} (hk : 0<k) {α β : ℝ}
    (hαβ : α≤β) (hβ : β<1) :
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, b ≤ Conclusion.bulkSize k L →
      Real.exp (-3*(Conclusion.bulkSize k L:ℝ)) ≤
        (1/2:ℝ)^b/(2*((b:ℝ)*(Real.exp (β*L)-Real.exp (α*L))+5)) := by
  filter_upwards [bin_denominator_eventually hk hβ,eventually_ge_atTop (0:ℝ)] with L hd hL
  intro b hb
  have hbb : (b:ℝ) ≤ Conclusion.bulkSize k L := by exact_mod_cast hb
  have hpow := (Real.exp_le_exp.mpr (neg_le_neg hbb)).trans (exp_neg_nat_le_half_pow b)
  have hex : Real.exp (α*L) ≤ Real.exp (β*L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hαβ hL)
  have hden : 0<2*((b:ℝ)*(Real.exp (β*L)-Real.exp (α*L))+5) := by positivity
  apply (le_div_iff₀ hden).mpr
  have hd' : 2*((b:ℝ)*(Real.exp (β*L)-Real.exp (α*L))+5) ≤
      Real.exp (2*(Conclusion.bulkSize k L:ℝ)) := by
    apply le_trans _ (hd b hb)
    have := Real.exp_pos (α*L)
    nlinarith [Nat.cast_nonneg (α := ℝ) b]
  calc
    _ ≤ Real.exp (-3*(Conclusion.bulkSize k L:ℝ))*Real.exp (2*(Conclusion.bulkSize k L:ℝ)) :=
      mul_le_mul_of_nonneg_left hd' (Real.exp_pos _).le
    _ = Real.exp (-(Conclusion.bulkSize k L:ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := hpow

end Ostmann.Construction

end

end OAI
