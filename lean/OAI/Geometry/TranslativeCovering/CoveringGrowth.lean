import OAI.Geometry.TranslativeCovering.RadialShell

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

namespace CoveringGrowth
open Filter Real
open scoped Topology

lemma polynomial {C δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k ≤ Real.exp (δ*(n:ℝ)) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) δ hδ).comp
    tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ => C*((n:ℝ)^k*Real.exp (-δ*(n:ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_natCast,mul_zero] using ht.const_mul C
  filter_upwards [ht'.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  have he := mul_le_mul_of_nonneg_right hn.le (Real.exp_pos (δ*(n:ℝ))).le
  have hid : Real.exp (-δ*(n:ℝ))*Real.exp (δ*(n:ℝ)) = 1 := by rw [← Real.exp_add]; convert Real.exp_zero using 2 ; ring
  calc
    _ = (C*((n:ℝ)^k*Real.exp (-δ*(n:ℝ))))*Real.exp (δ*(n:ℝ)) := by rw [mul_assoc,mul_assoc,hid,mul_one]
    _ ≤ _ := by simpa only [one_mul] using he

lemma moving_base {b : ℕ → ℝ} {B rate : ℝ} (hB : 0 < B)
    (hb : Tendsto b atTop (𝓝 B)) (hrate : Real.log B < rate) :
    ∀ᶠ n : ℕ in atTop,0 < b n ∧ (b n)^n ≤ Real.exp (rate*(n:ℝ)) := by
  have ht : Tendsto (fun n => Real.log (b n)) atTop (𝓝 (Real.log B)) :=
    (Real.continuousAt_log hB.ne').tendsto.comp hb
  filter_upwards [hb.eventually (lt_mem_nhds hB),ht.eventually (gt_mem_nhds hrate)] with n hn hlog
  refine ⟨hn,?_⟩
  calc
    _ = Real.exp ((n:ℝ)*Real.log (b n)) := by rw [Real.exp_nat_mul,Real.exp_log hn]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog.le (Nat.cast_nonneg n) |>.trans_eq (mul_comm _ _))

lemma combined {b : ℕ → ℝ} {B C rate : ℝ} (hB : 0 < B)
    (hb : Tendsto b atTop (𝓝 B)) (hrate : Real.log B < rate) (_hC : 0 ≤ C) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k*(b n)^n ≤ Real.exp (rate*(n:ℝ)) := by
  let rate₁ := (Real.log B+rate)/2
  have h₁ : Real.log B < rate₁ := by dsimp [rate₁]; linarith
  have h₂ : 0 < rate-rate₁ := by dsimp [rate₁]; linarith
  filter_upwards [moving_base hB hb h₁,polynomial (C := C) h₂ k] with n hn hp
  have hm := mul_le_mul hp hn.2 (pow_nonneg hn.1.le _) (Real.exp_pos ((rate-rate₁)*(n:ℝ))).le
  apply hm.trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

lemma union_decay {α β C : ℝ} (hαβ : α < β) (hβ : 0 < β) (hC : 0 < C) :
    Tendsto (fun n : ℕ => Real.exp (Real.exp (α*n)-C*Real.exp (β*n))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => Real.exp ((α-β)*(n:ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith : α-β<0)
  have hbig : Tendsto (fun n : ℕ => Real.exp (β*(n:ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hβ)
  have hprod : Tendsto (fun n : ℕ => (Real.exp ((α-β)*(n:ℝ))-C)*Real.exp (β*(n:ℝ))) atTop atBot :=
    (hbase.sub_const C).neg_mul_atTop (by simpa using neg_neg_of_pos hC) hbig
  have he (n : ℕ) : (Real.exp ((α-β)*(n:ℝ))-C)*Real.exp (β*(n:ℝ)) =
      Real.exp (α*n)-C*Real.exp (β*n) := by
    rw [sub_mul,← Real.exp_add]
    congr 2
    ring
  exact Real.tendsto_exp_atBot.comp (by simpa only [he] using hprod)

end CoveringGrowth

end OAI
