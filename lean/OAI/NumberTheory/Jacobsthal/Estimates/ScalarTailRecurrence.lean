import OAI.NumberTheory.Jacobsthal.Analysis.ThresholdFubini

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission

theorem quadratic_window_integral (l u e : ℝ) :
    (∫ y : ℝ in l..u,y^2-e)=(u^3-l^3)/3-e*(u-l) := by
  have hp : IntervalIntegrable (fun y : ℝ => y^2) volume l u :=
    (continuous_id.pow 2).intervalIntegrable l u
  have hc : IntervalIntegrable (fun _y : ℝ => e) volume l u := intervalIntegrable_const
  rw [intervalIntegral.integral_sub hp hc,integral_pow,intervalIntegral.integral_const]
  norm_num
  ring

theorem integrated_force_window (a l Y b e : ℝ) (hl : 0 ≤ l) (hb1 : 1 ≤ b) (hb2 : b ≤ 2)
    (hlT : l ≤ a/2+1) (hTY : a/2+b ≤ Y) :
    (∫ y : ℝ in l..Y,(y^2-e)*omissionForce .odd (2*y+2-a) b)=
      ∫ t : ℝ in 1..b,(((a/2+t)^3-l^3)/3-e*(a/2+t-l))/(t^2) := by
  have hlY : l ≤ Y := by linarith
  have hY : 0 ≤ Y := hl.trans hlY
  have hP : Measurable (fun y : ℝ => y^2-e) := (measurable_id.pow_const 2).sub measurable_const
  have hW : Measurable (fun t : ℝ => (t^2)⁻¹) := (measurable_id.pow_const 2).inv
  have hT : Measurable (fun t : ℝ => a/2+t) := measurable_const.add measurable_id
  have hPb : ∀ y ∈ Icc l Y,|y^2-e| ≤ Y^2+|e| := by
    intro y hy
    have hy0 : 0 ≤ y := hl.trans hy.1
    have hy2 : y^2 ≤ Y^2 := by nlinarith [hy.2]
    calc
      _ ≤ |y^2|+|e| := abs_sub _ _
      _ = y^2+|e| := by rw [abs_of_nonneg (sq_nonneg y)]
      _ ≤ _ := add_le_add hy2 le_rfl
  have hWb : ∀ t ∈ Icc (1:ℝ) b,|(t^2)⁻¹| ≤ 1 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
    apply (inv_le_one₀ (sq_pos_of_pos ht0)).mpr
    nlinarith [ht.1]
  have hTb : ∀ t ∈ Icc (1:ℝ) b,l ≤ a/2+t ∧ a/2+t ≤ Y := by
    intro t ht
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have h := weighted_threshold_swap hP hW hT l Y b (Y^2+|e|) 1
    (by positivity) (by norm_num) hPb hWb hTb
  have hinner (y : ℝ) :
      (∫ t in Icc (1:ℝ) b,if y<a/2+t then (t^2)⁻¹ else 0)=omissionForce .odd (2*y+2-a) b := by
    rw [force_as_threshold a y hb1 hb2,intervalIntegral.integral_of_le hb1,← integral_Icc_eq_integral_Ioc]
  simp_rw [hinner,quadratic_window_integral] at h
  rw [intervalIntegral.integral_of_le hlY,← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hb1,← integral_Icc_eq_integral_Ioc]
  rw [h]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _ht
  dsimp only
  ring

end ErdosOmissionBindings

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings.Audit
open ErdosContinuousOmission NumberTheoryLean.FinitePathGeometry

theorem literal_shifted_force (S a u y : ℝ) {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    omissionForce .odd (2*y+2-S-a-u) b=
      ∫ t : ℝ in 1..b,if y<(S+a+u)/2+t then (t^2)⁻¹ else 0 := by
  have he : 2*y+2-S-a-u=2*y+2-(S+a+u) := by ring
  rw [he,force_as_threshold (S+a+u) y hb1 hb2]

theorem literal_shifted_high_support (S y b : ℝ) (n : ℕ) (i : Side)
    (hy : S/2+(n:ℝ)+2 ≤ y) : gateIterate n omissionForce i (2*y+2-S) b=0 := by
  apply iterated_force_high_zero
  linarith

end ErdosOmissionBindings.Audit

end

section

open _root_.Set _root_.Erdos970.Set _root_.Filter _root_.Erdos970.Filter _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosOmissionBindings

theorem terminalBlock_high {r b : ℝ} (hr : 10 ≤ r) : terminalBlock r b=0 := by
  exact iterated_force_high_zero 2 .odd (by norm_num; exact hr)

theorem scalarFreeIterate_nonnegative {H : ScalarProfile} (hH : ∀ r b,0 ≤ H r b) (n : ℕ) :
    ∀ r b,0 ≤ scalarFreeIterate n H r b := by
  induction n with
  | zero => exact hH
  | succ n ih =>
    intro r b
    apply intervalIntegral.integral_nonneg_of_forall (baseCutoff_bounds b).1
    intro x
    exact div_nonneg (ih (r-x) x) (zero_le_one.trans (le_max_left _ _))

theorem scalarFreeIterate_high (n : ℕ) {r b : ℝ} (hr : 2*(n:ℝ)+10 ≤ r) :
    scalarFreeIterate n terminalBlock r b=0 := by
  induction n generalizing r b with
  | zero => exact terminalBlock_high (by simpa only [Nat.cast_zero,mul_zero,zero_add] using hr)
  | succ n ih =>
    rw [scalarFreeIterate,scalarFreeGate]
    calc
      _ = ∫ _x : ℝ in 1..baseCutoff b,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (baseCutoff_bounds b).1] at hx
        have hx2 : x ≤ 2 := hx.2.trans (baseCutoff_bounds b).2
        dsimp only
        rw [ih (by push_cast at hr; linarith : 2*(n:ℝ)+10 ≤ r-x),zero_div]
      _ = 0 := by simp

noncomputable def scalarTailIntegrand (n : ℕ) (S b y : ℝ) : ℝ :=
  2*y^2*scalarFreeIterate n terminalBlock (2*y+2-S) b
noncomputable def scalarTailMass (n : ℕ) (S b : ℝ) : ℝ :=
  ∫ y in Ioi 0,scalarTailIntegrand n S b y

theorem scalarTailIntegrand_continuous (n : ℕ) (S b : ℝ) : Continuous (scalarTailIntegrand n S b) := by
  have hb : Continuous (fun p : ℝ×ℝ => scalarFreeIterate n terminalBlock p.1 p.2) :=
    scalarFreeIterate_continuous terminalBlock_continuous n
  have hp : Continuous (fun y : ℝ => (2*y+2-S,b)) := by fun_prop
  have hc : Continuous (fun y : ℝ => scalarFreeIterate n terminalBlock (2*y+2-S) b) := hb.comp hp
  exact (continuous_const.mul (continuous_id.pow 2)).mul hc

theorem scalarTailIntegrand_nonnegative (n : ℕ) (S b y : ℝ) : 0 ≤ scalarTailIntegrand n S b y :=
  mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg y))
    (scalarFreeIterate_nonnegative terminalBlock_nonnegative n (2*y+2-S) b)

theorem scalarTailIntegrand_integrable (n : ℕ) (S b : ℝ) :
    IntegrableOn (scalarTailIntegrand n S b) (Ioi 0) := by
  let Y : ℝ := |S|+(n:ℝ)+5
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hc := (scalarTailIntegrand_continuous n S b).integrableOn_Icc (μ := volume) (a := 0) (b := Y)
  have hz : IntegrableOn (scalarTailIntegrand n S b) (Ioi Y) := by
    have hzero : IntegrableOn (fun _ : ℝ => (0:ℝ)) (Ioi Y) := integrable_zero ℝ ℝ _
    apply hzero.congr_fun _ measurableSet_Ioi
    intro y hy
    have hyY : Y < y := hy
    have hS := le_abs_self S
    have hS0 := abs_nonneg S
    have hh : 2*(n:ℝ)+10 ≤ 2*y+2-S := by dsimp [Y] at hyY; linarith
    simp only [scalarTailIntegrand,scalarFreeIterate_high n hh,mul_zero]
  have hu := hc.union hz
  rw [Icc_union_Ioi_eq_Ici hY] at hu
  exact hu.mono_set Ioi_subset_Ici_self

theorem scalarTailMass_nonnegative (n : ℕ) (S b : ℝ) : 0 ≤ scalarTailMass n S b :=
  integral_nonneg (scalarTailIntegrand_nonnegative n S b)

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

theorem evenDensity_indicator_integrable (n : ℕ) :
    IntegrableOn (fun y : ℝ => if 1 < y then omissionDensity n .even y else 0) (Ioi 0) := by
  change Integrable ((Ioi (1:ℝ)).indicator (omissionDensity n .even)) (volume.restrict (Ioi 0))
  rw [integrable_indicator_iff measurableSet_Ioi]
  change Integrable (omissionDensity n .even) ((volume.restrict (Ioi (0:ℝ))).restrict (Ioi 1))
  rw [Measure.restrict_restrict measurableSet_Ioi,inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))]
  exact omissionDensity_integrable n .even

theorem combinedDensity_integrable (n : ℕ) : IntegrableOn (combinedDensity n) (Ioi 0) :=
  (evenDensity_indicator_integrable n).add (omissionDensity_integrable n .odd)

theorem combinedDensity_integral (n : ℕ) :
    (∫ y in Ioi 0,combinedDensity n y)=omissionLossTerm n := by
  have he : (∫ y in Ioi (0:ℝ),if 1 < y then omissionDensity n .even y else 0)=
      ∫ y in Ioi 1,omissionDensity n .even y := by
    change (∫ y in Ioi (0:ℝ),(Ioi (1:ℝ)).indicator (omissionDensity n .even) y)=_
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))]
  unfold combinedDensity
  rw [integral_add (evenDensity_indicator_integrable n) (omissionDensity_integrable n .odd),he]
  rfl

theorem actual_loss_le_scalarTailMass (k : ℕ) : omissionLossTerm (k+2) ≤ scalarTailMass k 0 2 := by
  rw [← combinedDensity_integral]
  apply integral_mono_ae (combinedDensity_integrable (k+2)) (scalarTailIntegrand_integrable k 0 2)
  exact Filter.Eventually.of_forall (fun y => by
    simpa only [scalarTailIntegrand,sub_zero] using actual_combined_density_le k y)

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem omissionForce_le_one (i : Side) (r b : ℝ) : omissionForce i r b ≤ 1 := by
  cases i with
  | even => norm_num [omissionForce]
  | odd =>
    have hc := (upperCutoff_bounds .odd r b).1
    have hb : 0 ≤ (baseCutoff b)⁻¹ := inv_nonneg.mpr (by linarith [(baseCutoff_bounds b).1])
    have hi : (upperCutoff .odd r b)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by linarith : 0 < upperCutoff .odd r b)).mpr hc
    unfold omissionForce survivorBaseline
    linarith

theorem freeGate_le_one {H : Profile} (hH : JointContinuous H)
    (hupper : ∀ i r b,H i r b ≤ 1) (i : Side) (r b : ℝ) : freeGate H i r b ≤ 1 := by
  have hc := gate_integrand_continuous hH i r
  have hi := intervalIntegral.integral_mono_on (baseCutoff_bounds b).1
    (hc.intervalIntegrable (μ := volume) 1 (baseCutoff b))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 1 (baseCutoff b))
    (fun x _ => (div_le_one (by linarith [le_max_left (1:ℝ) x] : 0 < max 1 x)).mpr
      ((hupper i.flip (r-x) x).trans (le_max_left _ _)))
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one] at hi
  exact hi.trans (by linarith [(baseCutoff_bounds b).2])

theorem gateIterate_force_le_one (n : ℕ) (i : Side) (r b : ℝ) : gateIterate n omissionForce i r b ≤ 1 := by
  induction n generalizing i r b with
  | zero => exact omissionForce_le_one i r b
  | succ n ih =>
    exact (gate_le_freeGate (gateIterate_continuous omissionForce_continuous n)
      (gateIterate_nonnegative omissionForce_nonnegative n) i r b).trans
      (freeGate_le_one (gateIterate_continuous omissionForce_continuous n) ih i r b)

theorem terminalBlock_le_one (r b : ℝ) : terminalBlock r b ≤ 1 := gateIterate_force_le_one 2 .odd r b

theorem scalarFreeIterate_le_one (n : ℕ) (r b : ℝ) : scalarFreeIterate n terminalBlock r b ≤ 1 := by
  induction n generalizing r b with
  | zero => exact terminalBlock_le_one r b
  | succ n ih =>
    exact freeGate_le_one (H := fun _ => scalarFreeIterate n terminalBlock)
      (fun _ => scalarFreeIterate_continuous terminalBlock_continuous n) (fun _ => ih) .even r b

theorem scalar_weighted_bound (n : ℕ) (S b : ℝ) {y Y : ℝ} (hy0 : 0 ≤ y) (hyY : y ≤ Y) :
    |scalarTailIntegrand n S b y| ≤ 2*Y^2 := by
  rw [abs_of_nonneg (scalarTailIntegrand_nonnegative n S b y)]
  have hh := scalarFreeIterate_le_one n (2*y+2-S) b
  have hp := mul_le_mul_of_nonneg_left hh (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg y))
  unfold scalarTailIntegrand
  nlinarith

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.Filter _root_.Erdos970.Filter _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosOmissionBindings

theorem scalarTailMass_bounded (n : ℕ) (S b Y : ℝ) (hY : 0 ≤ Y)
    (hhigh : S/2+(n:ℝ)+4 ≤ Y) :
    scalarTailMass n S b=∫ y : ℝ in 0..Y,scalarTailIntegrand n S b y := by
  have hz : (∫ y in Ioi Y,scalarTailIntegrand n S b y)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    change Y < y at hy
    have hh : 2*(n:ℝ)+10 ≤ 2*y+2-S := by linarith
    simp only [scalarTailIntegrand,scalarFreeIterate_high n hh,mul_zero]
  have hh := intervalIntegral.integral_Ioi_sub_Ioi (scalarTailIntegrand_integrable n S b) hY
  rw [hz,sub_zero] at hh
  exact hh

theorem scalarTailMass_succ (n : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass (n+1) S b=∫ x : ℝ in 1..b,scalarTailMass n (S+x) x/x := by
  let Y : ℝ := S/2+(n:ℝ)+5
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  let G : ℝ×ℝ → ℝ := fun p =>
    2*p.1^2*scalarFreeIterate n terminalBlock (2*p.1+2-S-p.2) p.2/(max 1 p.2)
  have hpmap : Continuous (fun p : ℝ×ℝ => (2*p.1+2-S-p.2,p.2)) := by fun_prop
  have hphi : Continuous (fun p : ℝ×ℝ => scalarFreeIterate n terminalBlock (2*p.1+2-S-p.2) p.2) :=
    (scalarFreeIterate_continuous terminalBlock_continuous n).comp hpmap
  have hG : Continuous G := by
    apply ((continuous_const.mul (continuous_fst.pow 2)).mul hphi).div
      (continuous_const.max continuous_snd)
    intro p
    exact ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _))
  have hbnd : ∀ y ∈ Icc (0:ℝ) Y,∀ x ∈ Icc (1:ℝ) b,|G (y,x)| ≤ 2*Y^2 := by
    intro y hy x _hx
    have hp := scalarFreeIterate_nonnegative terminalBlock_nonnegative n (2*y+2-S-x) x
    have hu := scalarFreeIterate_le_one n (2*y+2-S-x) x
    have hn : 0 ≤ 2*y^2*scalarFreeIterate n terminalBlock (2*y+2-S-x) x := by positivity
    have hh := mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg y))
    dsimp only [G]
    rw [abs_of_nonneg (div_nonneg hn (zero_le_one.trans (le_max_left _ _)))]
    apply (div_le_self hn (le_max_left (1:ℝ) x)).trans
    nlinarith [hy.1,hy.2]
  have hswap := bounded_rectangle_swap hG.measurable 0 Y 1 b (2*Y^2) hbnd
  have hswap' : (∫ y : ℝ in 0..Y,∫ x : ℝ in 1..b,G (y,x))=
      ∫ x : ℝ in 1..b,∫ y : ℝ in 0..Y,G (y,x) := by
    simpa only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hY,
      ← intervalIntegral.integral_of_le hb1] using hswap
  rw [scalarTailMass_bounded (n+1) S b Y hY (by dsimp [Y]; push_cast; linarith)]
  have hleft : (∫ y : ℝ in 0..Y,scalarTailIntegrand (n+1) S b y)=
      ∫ y : ℝ in 0..Y,∫ x : ℝ in 1..b,G (y,x) := by
    apply intervalIntegral.integral_congr
    intro y _hy
    simp only [scalarTailIntegrand,scalarFreeIterate,scalarFreeGate,baseCutoff_on hb1 hb2,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [G]
    ring
  rw [hleft,hswap']
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hb1] at hx
  have hx2 : x ≤ 2 := hx.2.trans hb2
  dsimp only
  rw [scalarTailMass_bounded n (S+x) x Y hY (by dsimp [Y]; linarith),← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp only [G,scalarTailIntegrand]
  rw [max_eq_right hx.1]
  have he : 2*y+2-S-x=2*y+2-(S+x) := by ring
  rw [he]

end ErdosOmissionTail

end

end Erdos970

end OAI
