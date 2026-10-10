import OAI.NumberTheory.Jacobsthal.Estimates.ScalarTailRecurrence

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary ErdosOmissionBindings
open NumberTheoryLean.FinitePathGeometry

theorem terminalBlock_mask (S y : ℝ) {b : ℝ} (_hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    terminalBlock (2*y+2-S) b=
      ∫ a in Icc (1:ℝ) b,if S/2+a ≤ y then
        gate omissionForce .even (2*y+2-S-a) a/(max 1 a) else 0 := by
  have hset : Ioc (1:ℝ) (upperCutoff .odd (2*y+2-S) b)=
      Ioc (1:ℝ) b ∩ {a : ℝ | S/2+a ≤ y} := by
    ext a
    constructor
    · intro ha
      obtain ⟨ha1,ha2,hab,hgate⟩ := (mem_upperCutoff .odd (2*y+2-S) b a).mp ha
      have hh := (strong_gate_below_two ha2).mp hgate
      exact ⟨⟨ha1,hab⟩,by change S/2+a ≤ y; linarith⟩
    · rintro ⟨⟨ha1,hab⟩,hy⟩
      apply (mem_upperCutoff .odd (2*y+2-S) b a).mpr
      refine ⟨ha1,hab.trans hb2,hab,?_⟩
      apply (strong_gate_below_two (hab.trans hb2)).mpr
      change S/2+a ≤ y at hy
      linarith
  have hm : MeasurableSet {a : ℝ | S/2+a ≤ y} :=
    measurableSet_le (measurable_const.add measurable_id) measurable_const
  change (∫ a : ℝ in 1..upperCutoff .odd (2*y+2-S) b,
    gate omissionForce .even (2*y+2-S-a) a/(max 1 a))=_
  rw [intervalIntegral.integral_of_le (upperCutoff_bounds .odd (2*y+2-S) b).1,
    hset,← setIntegral_indicator hm,← integral_Icc_eq_integral_Ioc]
  rfl

noncomputable def terminalOuterIntegrand (S : ℝ) (p : ℝ×ℝ) : ℝ :=
  if S/2+p.2 ≤ p.1 then
    2*p.1^2*gate omissionForce .even (2*p.1+2-S-p.2) p.2/(max 1 p.2) else 0

theorem terminalOuterIntegrand_measurable (S : ℝ) : Measurable (terminalOuterIntegrand S) := by
  have hc0 : Continuous (fun p : ℝ×ℝ => gate omissionForce .even p.1 p.2) :=
    gate_continuous omissionForce_continuous .even
  have hp : Continuous (fun p : ℝ×ℝ => (2*p.1+2-S-p.2,p.2)) := by fun_prop
  have hc : Continuous (fun p : ℝ×ℝ => gate omissionForce .even (2*p.1+2-S-p.2) p.2) := hc0.comp hp
  exact Measurable.ite (measurableSet_le (measurable_const.add measurable_snd) measurable_fst)
    (((measurable_const.mul (measurable_fst.pow_const 2)).mul hc.measurable).div
      (measurable_const.max measurable_snd)) measurable_const

theorem terminalOuterIntegrand_bound (S a : ℝ) {y Y : ℝ} (hy0 : 0 ≤ y) (hyY : y ≤ Y) :
    |terminalOuterIntegrand S (y,a)| ≤ 2*Y^2 := by
  unfold terminalOuterIntegrand
  split_ifs
  · have hp := gate_nonnegative omissionForce_nonnegative .even (2*y+2-S-a) a
    have hu := gateIterate_force_le_one 1 .even (2*y+2-S-a) a
    change gate omissionForce .even (2*y+2-S-a) a ≤ 1 at hu
    have hn : 0 ≤ 2*y^2*gate omissionForce .even (2*y+2-S-a) a := by positivity
    have hm := mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg y))
    rw [abs_of_nonneg (div_nonneg hn (zero_le_one.trans (le_max_left _ _)))]
    apply (div_le_self hn (le_max_left (1:ℝ) a)).trans
    nlinarith
  · simpa only [abs_zero] using mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg Y)

theorem scalarTailMass_zero_outer {S b : ℝ} (hS : 0 ≤ S) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass 0 S b=
      ∫ a : ℝ in 1..b,(2/a)*(∫ y : ℝ in S/2+a..S/2+4,
        y^2*gate omissionForce .even (2*y+2-S-a) a) := by
  let Y : ℝ := S/2+4
  have hY : 0 ≤ Y := by dsimp [Y]; linarith
  have hl (y : ℝ) : scalarTailIntegrand 0 S b y=∫ a in Icc (1:ℝ) b,terminalOuterIntegrand S (y,a) := by
    change 2*y^2*terminalBlock (2*y+2-S) b=_
    rw [terminalBlock_mask S y hb1 hb2,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with a
    dsimp only [terminalOuterIntegrand]
    split_ifs <;> ring
  have hs := bounded_rectangle_swap (terminalOuterIntegrand_measurable S) 0 Y 1 b (2*Y^2)
    (fun y hy a _ha => terminalOuterIntegrand_bound S a hy.1 hy.2)
  have hr (a : ℝ) (ha : a ∈ Icc (1:ℝ) b) :
      (∫ y in Icc (0:ℝ) Y,terminalOuterIntegrand S (y,a))=
        (2/a)*(∫ y : ℝ in S/2+a..Y,y^2*gate omissionForce .even (2*y+2-S-a) a) := by
    have ha2 : a ≤ 2 := ha.2.trans hb2
    have hlo : 0 ≤ S/2+a := by linarith [ha.1]
    have hhi : S/2+a ≤ Y := by dsimp [Y]; linarith
    have hset : Icc (0:ℝ) Y ∩ Ici (S/2+a)=Icc (S/2+a) Y := by
      ext y
      constructor
      · rintro ⟨hy,hylo⟩; exact ⟨hylo,hy.2⟩
      · intro hy; exact ⟨⟨hlo.trans hy.1,hy.2⟩,hy.1⟩
    have he : (fun y : ℝ => terminalOuterIntegrand S (y,a))=
        (Ici (S/2+a)).indicator (fun y => (2/a)*(y^2*gate omissionForce .even (2*y+2-S-a) a)) := by
      funext y
      unfold terminalOuterIntegrand
      by_cases h : S/2+a ≤ y
      · rw [ite_eq_left h,indicator_of_mem (show y ∈ Ici (S/2+a) from h),max_eq_right ha.1]
        ring
      · rw [ite_eq_right h,indicator_of_notMem (show y ∉ Ici (S/2+a) from h)]
    rw [he,setIntegral_indicator measurableSet_Ici,hset,integral_const_mul,
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hhi]
  rw [scalarTailMass_bounded 0 S b Y hY (by dsimp [Y]; norm_num),
    intervalIntegral.integral_of_le hY,← integral_Icc_eq_integral_Ioc]
  simp_rw [hl]
  rw [hs,intervalIntegral.integral_of_le hb1,← integral_Icc_eq_integral_Ioc]
  exact setIntegral_congr_fun measurableSet_Icc hr

end ErdosOmissionTail

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary ErdosOmissionBindings
open NumberTheoryLean.FinitePathGeometry

theorem evenGate_weighted_swap (S a l Y : ℝ) (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    (hl : 0 ≤ l) (hlY : l ≤ Y) :
    (∫ y : ℝ in l..Y,y^2*gate omissionForce .even (2*y+2-S-a) a)=
      ∫ u : ℝ in 1..a,(∫ y : ℝ in l..Y,y^2*omissionForce .odd (2*y+2-S-a-u) u)/u := by
  let G : ℝ×ℝ → ℝ := fun p => p.1^2*omissionForce .odd (2*p.1+2-S-a-p.2) p.2/(max 1 p.2)
  have hpmap : Continuous (fun p : ℝ×ℝ => (2*p.1+2-S-a-p.2,p.2)) := by fun_prop
  have hc : Continuous (fun p : ℝ×ℝ => omissionForce .odd (2*p.1+2-S-a-p.2) p.2) :=
    (omissionForce_continuous .odd).comp hpmap
  have hG : Continuous G := by
    apply ((continuous_fst.pow 2).mul hc).div (continuous_const.max continuous_snd)
    intro p
    exact ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _))
  have hbnd : ∀ y ∈ Icc l Y,∀ u ∈ Icc (1:ℝ) a,|G (y,u)| ≤ Y^2 := by
    intro y hy u _hu
    have hy0 : 0 ≤ y := hl.trans hy.1
    have hp := omissionForce_nonnegative .odd (2*y+2-S-a-u) u
    have hu := omissionForce_le_one .odd (2*y+2-S-a-u) u
    have hn : 0 ≤ y^2*omissionForce .odd (2*y+2-S-a-u) u := by positivity
    have hh := mul_le_mul_of_nonneg_left hu (sq_nonneg y)
    dsimp only [G]
    rw [abs_of_nonneg (div_nonneg hn (zero_le_one.trans (le_max_left _ _)))]
    apply (div_le_self hn (le_max_left (1:ℝ) u)).trans
    nlinarith [hy.2]
  have hs := bounded_rectangle_swap hG.measurable l Y 1 a (Y^2) hbnd
  have hs' : (∫ y : ℝ in l..Y,∫ u : ℝ in 1..a,G (y,u))=
      ∫ u : ℝ in 1..a,∫ y : ℝ in l..Y,G (y,u) := by
    simpa only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hlY,
      ← intervalIntegral.integral_of_le ha1] using hs
  have hl' : (∫ y : ℝ in l..Y,y^2*gate omissionForce .even (2*y+2-S-a) a)=
      ∫ y : ℝ in l..Y,∫ u : ℝ in 1..a,G (y,u) := by
    apply intervalIntegral.integral_congr
    intro y _hy
    dsimp only
    rw [gate,show upperCutoff .even (2*y+2-S-a) a=a from baseCutoff_on ha1 ha2,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _hu
    dsimp only [G,Side.flip]
    ring
  rw [hl',hs']
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha1] at hu
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp only [G]
  rw [max_eq_right hu.1]

theorem scalarTailMass_zero_triple {S b : ℝ} (hS : 0 ≤ S) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass 0 S b=
      ∫ a : ℝ in 1..b,∫ u : ℝ in 1..a,∫ c : ℝ in 1..u,
        lastWindowCoefficient S a u c/(a*u*c) := by
  rw [scalarTailMass_zero_outer hS hb1 hb2]
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le hb1] at ha
  have ha2 : a ≤ 2 := ha.2.trans hb2
  have hl : 0 ≤ S/2+a := by linarith [ha.1]
  have hlY : S/2+a ≤ S/2+4 := by linarith
  dsimp only
  rw [evenGate_weighted_swap S a (S/2+a) (S/2+4) ha.1 ha2 hl hlY,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha.1] at hu
  have hu2 : u ≤ 2 := hu.2.trans ha2
  have hw := integrated_force_window (S+a+u) (S/2+a) (S/2+4) u 0 hl hu.1 hu2
    (by linarith [hu.1]) (by linarith)
  simp only [sub_zero,zero_mul] at hw
  have hgap (y : ℝ) : 2*y+2-S-a-u=2*y+2-(S+a+u) := by ring
  dsimp only
  simp_rw [hgap]
  rw [hw,← intervalIntegral.integral_div,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro c hc
  rw [uIcc_of_le hu.1] at hc
  have ha0 : a ≠ 0 := by linarith [ha.1]
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have hc0 : c ≠ 0 := by linarith [hc.1]
  dsimp only [lastWindowCoefficient]
  field_simp
  ring

end ErdosOmissionTail

end

end Erdos970

end OAI
