import OAI.NumberTheory.Jacobsthal.Analysis.OrderedTriangleFubini

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission

theorem force_as_threshold (a y : ℝ) {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    omissionForce .odd (2*y+2-a) b=
      ∫ t : ℝ in 1..b,if y<a/2+t then (t^2)⁻¹ else 0 := by
  classical
  let r := 2*y+2-a
  have hb : baseCutoff b=b := baseCutoff_on hb1 hb2
  have hc : upperCutoff .odd r b ≤ b := by simpa only [hb] using cutoff_le_base .odd r b
  have hset : Ioc (upperCutoff .odd r b) b=Ioc (1:ℝ) b ∩ {t : ℝ | y<a/2+t} := by
    ext t
    have he := literal_omission_window r b t
    rw [hb] at he
    constructor
    · intro ht
      obtain ⟨ht1,ht2,htb,hbad⟩ := he.mp ht
      refine ⟨⟨ht1,htb⟩,?_⟩
      rw [strong_gate_below_two ht2] at hbad
      have hh := lt_of_not_ge hbad
      change y<a/2+t
      dsimp [r] at hh
      linarith
    · rintro ⟨⟨ht1,htb⟩,hy⟩
      apply he.mpr
      refine ⟨ht1,htb.trans hb2,htb,?_⟩
      rw [strong_gate_below_two (htb.trans hb2)]
      intro hgate
      change y<a/2+t at hy
      dsimp [r] at hgate
      linarith
  have hm : MeasurableSet {t : ℝ | y<a/2+t} :=
    measurableSet_lt measurable_const (measurable_const.add measurable_id)
  rw [omissionForce_odd_integral,hb,intervalIntegral.integral_of_le hc,intervalIntegral.integral_of_le hb1]
  change (∫ t in Ioc (upperCutoff .odd r b) b,(t^2)⁻¹)=
    ∫ t in Ioc (1:ℝ) b,({t : ℝ | y<a/2+t}).indicator (fun t => (t^2)⁻¹) t
  rw [setIntegral_indicator hm,hset]

theorem force_high_zero (i : Side) {r b : ℝ} (hr : 6 ≤ r) : omissionForce i r b=0 := by
  cases i with
  | even => rfl
  | odd =>
    have hc : upperCutoff .odd r b=baseCutoff b := by
      change max 1 (min (min 2 b) ((r-2)/2))=max 1 (min 2 b)
      rw [min_eq_left ((min_le_left 2 b).trans (by linarith))]
    simp only [omissionForce,hc,survivorBaseline,sub_self]

theorem iterated_force_high_zero (n : ℕ) (i : Side) {r b : ℝ}
    (hr : 2*(n:ℝ)+6 ≤ r) : gateIterate n omissionForce i r b=0 := by
  induction n generalizing i r b with
  | zero => exact force_high_zero i (by simpa only [Nat.cast_zero,mul_zero,zero_add] using hr)
  | succ n ih =>
    rw [gateIterate,gate]
    calc
      _ = ∫ _x : ℝ in 1..upperCutoff i r b,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
        dsimp only
        have hx2 : x ≤ 2 := hx.2.trans (upperCutoff_bounds i r b).2
        rw [ih i.flip (by push_cast at hr; linarith : 2*(n:ℝ)+6 ≤ r-x),zero_div]
      _ = 0 := by simp

theorem omissionDensity_high_zero (n : ℕ) (i : Side) {y : ℝ} (hy : (n:ℝ)+2 ≤ y) :
    omissionDensity n i y=0 := by
  rw [omissionDensity,iterated_force_high_zero n i (by linarith : 2*(n:ℝ)+6 ≤ 2*y+2),mul_zero]

end ErdosOmissionBindings

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission

theorem second_loss_bounded : omissionLossTerm 1=∫ y : ℝ in 1..3,omissionDensity 1 .even y := by
  have ho : (∫ y in sourceDomain .odd,omissionDensity 1 .odd y)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y _hy
    have h := (omission_wrong_parity_zero 0).2 (2*y+2) 2
    norm_num only [Nat.mul_zero,Nat.zero_add] at h
    rw [omissionDensity,h,mul_zero]
  have hz : (∫ y in Ioi 3,omissionDensity 1 .even y)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact omissionDensity_high_zero 1 .even (by norm_num; change 3<y at hy; linarith)
  have h := intervalIntegral.integral_Ioi_sub_Ioi (omissionDensity_integrable 1 .even) (by norm_num : (1:ℝ)≤3)
  rw [hz,sub_zero] at h
  rw [omissionLossTerm,ho,add_zero]
  exact h

theorem third_loss_bounded : omissionLossTerm 2=∫ y : ℝ in 0..4,omissionDensity 2 .odd y := by
  have he : (∫ y in sourceDomain .even,omissionDensity 2 .even y)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y _hy
    have h := (omission_wrong_parity_zero 1).1 (2*y+2) 2
    norm_num only [Nat.mul_one] at h
    rw [omissionDensity,h,mul_zero]
  have hz : (∫ y in Ioi 4,omissionDensity 2 .odd y)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact omissionDensity_high_zero 2 .odd (by norm_num; change 4<y at hy; linarith)
  have h := intervalIntegral.integral_Ioi_sub_Ioi (omissionDensity_integrable 2 .odd) (by norm_num : (0:ℝ)≤4)
  rw [hz,sub_zero] at h
  rw [omissionLossTerm,he,zero_add]
  exact h

end ErdosOmissionBindings

end

end Erdos970

end OAI
