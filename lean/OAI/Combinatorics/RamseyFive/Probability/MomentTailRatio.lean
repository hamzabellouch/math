import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

lemma moment_tail_ratio {B κ α P : ℝ} (hB : 0<B) (p : ℕ) :
    (B^p*Real.exp (-α*((p:ℝ)*P)))/(B*Real.exp (-κ)/10)^p =
      Real.exp ((p:ℝ)*(κ+Real.log 10-α*P)) := by
  have ht : B*Real.exp (-κ)/10=B*Real.exp (-(κ+Real.log 10)) := by
    rw [neg_add,Real.exp_add,Real.exp_neg (Real.log 10),Real.exp_log (by norm_num : (0:ℝ)<10)]
    ring
  rw [ht,mul_pow,←Real.exp_nat_mul]
  have he : -α*((p:ℝ)*P)=((p:ℝ)*(κ+Real.log 10-α*P))+(p:ℝ)*(-(κ+Real.log 10)) := by ring
  rw [he,Real.exp_add]
  field_simp

lemma validation_tail_ratio {B κ P : ℝ} (hB : 0<B)
    (hκ : κ+Real.log 10≤P/20) :
    (B^2*Real.exp (-3*P/5))/(B*Real.exp (-κ)/10)^2≤Real.exp (-P/2) := by
  have he : -3*P/5=-(3/10:ℝ)*((2:ℝ)*P) := by ring
  have hr := moment_tail_ratio (κ:=κ) (α:=3/10) (P:=P) hB 2
  norm_num only [Nat.cast_ofNat] at hr
  rw [←he] at hr
  rw [hr]
  apply Real.exp_le_exp.mpr
  linarith only [hκ]

lemma high_tail_ratio {B κ P : ℝ} (hB : 0<B)
    (p : ℕ) (hκ : κ+Real.log 10≤P/20) :
    (B^p*Real.exp (-(1/10:ℝ)*((p:ℝ)*P)))/(B*Real.exp (-κ)/10)^p≤
      Real.exp (-((p:ℝ)*P)/20) := by
  rw [moment_tail_ratio hB p]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hκ (Nat.cast_nonneg p)
  linarith only [h]

lemma high_tail_polynomial {B κ P q : ℝ} (hB : 0<B) (hq : 0<q)
    (p : ℕ) (hκ : κ+Real.log 10≤P/20) (hp : 1000*Real.log q≤(p:ℝ)*P) :
    (B^p*Real.exp (-(1/10:ℝ)*((p:ℝ)*P)))/(B*Real.exp (-κ)/10)^p≤q^(-(50:ℝ)) := by
  apply (high_tail_ratio hB p hκ).trans
  rw [Real.rpow_def_of_pos hq]
  exact Real.exp_le_exp.mpr (by linarith only [hp])

lemma exceptional_scales {L f B z q : ℝ} {R : ℕ} (hL : 0≤L)
    (hf : f≤2/25) (hB : 0≤B) (_hq : 0<q)
    (hR : (R:ℝ)*Real.exp (-(23/25:ℝ)*L)≤1/10)
    (herr : B*Real.exp (-(91/100:ℝ)*L)≤z/(100*q)) :
    let b := Real.exp (-L*(1-f))
    b∈Set.Icc 0 1 ∧ 9/10≤(1-b)^R ∧ b*(B*Real.exp (L/100))≤z/(100*q) := by
  dsimp only
  have hbpos : 0<Real.exp (-L*(1-f)) := Real.exp_pos _
  have hb : Real.exp (-L*(1-f))≤Real.exp (-(23/25:ℝ)*L) :=
    Real.exp_le_exp.mpr (by nlinarith only [hL,hf])
  have hb1 : Real.exp (-L*(1-f))≤1 := Real.exp_le_one_iff.mpr (by nlinarith only [hL,hf])
  refine ⟨⟨hbpos.le,hb1⟩,?_,?_⟩
  · have hbern := one_add_mul_le_pow (show -2≤-Real.exp (-L*(1-f)) by linarith only [hb1]) R
    have hr := (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg R)).trans hR
    have he : 1+-Real.exp (-L*(1-f))=1-Real.exp (-L*(1-f)) := by ring
    rw [he] at hbern
    linarith only [hbern,hr]
  · apply le_trans (mul_le_mul_of_nonneg_right hb (mul_nonneg hB (Real.exp_pos _).le))
    calc
      _ = B*(Real.exp (-(23/25:ℝ)*L)*Real.exp (L/100)) := by ring
      _ = B*Real.exp (-(91/100:ℝ)*L) := by rw [←Real.exp_add];congr 2;ring
      _ ≤ _ := herr

end SharpRamseyFive.ScoreScalars

end OAI
