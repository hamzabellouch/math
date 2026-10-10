import OAI.NumberTheory.Jacobsthal.Analysis.ActualLossDensity
import OAI.NumberTheory.Jacobsthal.Analysis.OmissionForceIntegral

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
open _root_.Filter _root_.Erdos970.Filter
namespace ErdosContinuousOmission
open NumberTheoryLean.FinitePathGeometry
open ErdosBoundaryIntegral Erdos970Dependency.StandardBoundary

theorem omission_integral_hasSum (i : Side) :
    HasSum (fun n : ℕ => ∫ y in sourceDomain i,omissionDensity n i y)
      (∫ y in sourceDomain i,lossDensity i y) := by
  have hmeas : MeasurableSet (sourceDomain i) := by cases i <;> exact measurableSet_Ioi
  apply hasSum_integral_of_dominated_convergence (fun n y => omissionDensity n i y)
    (fun n => (omissionDensity_continuous n i).aestronglyMeasurable.restrict)
  · intro n
    filter_upwards [ae_restrict_mem hmeas] with y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (omissionDensity_nonnegative n i hy)]
  · exact Eventually.of_forall (fun y => (lossDensity_hasSum i y).summable)
  · apply (lossDensity_integrable i).congr
    exact Eventually.of_forall (fun y => (lossDensity_hasSum i y).tsum_eq.symm)
  · exact Eventually.of_forall (lossDensity_hasSum i)

noncomputable def omissionLossTerm (n : ℕ) : ℝ :=
  (∫ y in sourceDomain .even,omissionDensity n .even y)+
    ∫ y in sourceDomain .odd,omissionDensity n .odd y

theorem omissionLossTerm_nonnegative (n : ℕ) : 0 ≤ omissionLossTerm n := by
  unfold omissionLossTerm
  apply add_nonneg
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet (sourceDomain .even) from measurableSet_Ioi)] with y hy
    exact omissionDensity_nonnegative n .even hy
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet (sourceDomain .odd) from measurableSet_Ioi)] with y hy
    exact omissionDensity_nonnegative n .odd hy

theorem actual_signed_loss_hasSum :
    HasSum omissionLossTerm (standardCoefficient-signedCoefficientI) := by
  rw [actual_loss_integral]
  exact (omission_integral_hasSum .even).add (omission_integral_hasSum .odd)

theorem actual_signed_loss_series :
    (8:ℝ)/3-signedCoefficientI=∑' n : ℕ,omissionLossTerm n := by
  have h := actual_signed_loss_hasSum.tsum_eq
  rw [standard_coefficient_eq] at h
  exact h.symm

theorem actual_loss_summable : Summable omissionLossTerm := actual_signed_loss_hasSum.summable

theorem actual_coefficient_le_standard : signedCoefficientI ≤ (8:ℝ)/3 := by
  have h : 0 ≤ (∑' n : ℕ,omissionLossTerm n) := tsum_nonneg omissionLossTerm_nonnegative
  rw [← actual_signed_loss_series] at h
  linarith

end ErdosContinuousOmission

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosContinuousOmission
open NumberTheoryLean.FinitePathGeometry

theorem gate_zero_of_side (H : Profile) (i : Side)
    (hH : ∀ r b,H i.flip r b=0) (r b : ℝ) : gate H i r b=0 := by
  simp only [gate,hH,zero_div,intervalIntegral.integral_zero]

theorem omission_wrong_parity_zero (n : ℕ) :
    (∀ r b,gateIterate (2*n) omissionForce .even r b=0) ∧
      (∀ r b,gateIterate (2*n+1) omissionForce .odd r b=0) := by
  induction n with
  | zero =>
    constructor
    · intro r b; rfl
    · intro r b
      exact gate_zero_of_side omissionForce .odd (fun _ _ => rfl) r b
  | succ n ih =>
    have hE : ∀ r b,gateIterate (2*(n+1)) omissionForce .even r b=0 := by
      intro r b
      rw [show 2*(n+1)=(2*n+1)+1 by omega,gateIterate]
      exact gate_zero_of_side (gateIterate (2*n+1) omissionForce) .even ih.2 r b
    refine ⟨hE,?_⟩
    intro r b
    rw [gateIterate]
    exact gate_zero_of_side (gateIterate (2*(n+1)) omissionForce) .odd hE r b

end ErdosContinuousOmission

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
open _root_.Filter _root_.Erdos970.Filter
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem omissionDensity_integrable (n : ℕ) (i : Side) :
    IntegrableOn (omissionDensity n i) (sourceDomain i) := by
  have hm : MeasurableSet (sourceDomain i) := by cases i <;> exact measurableSet_Ioi
  apply (lossDensity_integrable i).mono' (omissionDensity_continuous n i).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem hm] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg (omissionDensity_nonnegative n i hy)]
  have h := (lossDensity_hasSum i y).summable.sum_le_tsum ({n}:Finset ℕ)
    (fun k _ => omissionDensity_nonnegative k i hy)
  simpa only [Finset.sum_singleton,(lossDensity_hasSum i y).tsum_eq] using h

theorem first_odd_density_low {y : ℝ} (hy : y ≤ 1) : omissionDensity 0 .odd y=y^2 := by
  have hc : upperCutoff .odd (2*y+2) 2=1 := upperCutoff_odd_small (by linarith)
  norm_num [omissionDensity,sourceWeight,gateIterate,omissionForce,hc,survivorBaseline,baseCutoff]
  ring

theorem first_odd_density_middle {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y ≤ 2) :
    omissionDensity 0 .odd y=2*y-y^2 := by
  have hc : upperCutoff .odd (2*y+2) 2=y := by
    change max 1 (min (min 2 2) ((2*y+2-2)/2))=y
    have he : (2*y+2-2)/2=y := by ring
    rw [he,min_self,min_eq_right hy2,max_eq_right hy1]
  have hn : y ≠ 0 := by linarith
  norm_num [omissionDensity,sourceWeight,gateIterate,omissionForce,hc,survivorBaseline,baseCutoff]
  field_simp

theorem first_odd_density_high {y : ℝ} (hy : 2 ≤ y) : omissionDensity 0 .odd y=0 := by
  have hc : upperCutoff .odd (2*y+2) 2=2 := by
    change max 1 (min (min 2 2) ((2*y+2-2)/2))=2
    have he : (2*y+2-2)/2=y := by ring
    rw [he,min_self,min_eq_left hy,max_eq_right (by norm_num : (1:ℝ)≤2)]
  norm_num [omissionDensity,sourceWeight,gateIterate,omissionForce,hc,survivorBaseline,baseCutoff]

theorem actual_first_loss_eq_one : omissionLossTerm 0=1 := by
  have he : (∫ y in sourceDomain .even,omissionDensity 0 .even y)=0 := by
    simp [omissionDensity,sourceWeight,gateIterate,omissionForce]
  have hz : (∫ y in Ioi 2,omissionDensity 0 .odd y)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact first_odd_density_high (le_of_lt hy)
  have hlow : (∫ y : ℝ in 0..1,omissionDensity 0 .odd y)=(1:ℝ)/3 := by
    calc
      _ = ∫ y : ℝ in 0..1,y^2 := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hy
        exact first_odd_density_low hy.2
      _ = _ := by norm_num
  have hmid : (∫ y : ℝ in 1..2,omissionDensity 0 .odd y)=(2:ℝ)/3 := by
    calc
      _ = ∫ y : ℝ in 1..2,2*y-y^2 := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hy
        exact first_odd_density_middle hy.1 hy.2
      _ = _ := by
        have hl : IntervalIntegrable (fun y : ℝ => 2*y) volume 1 2 :=
          (continuous_const.mul continuous_id).intervalIntegrable 1 2
        have hq : IntervalIntegrable (fun y : ℝ => y^2) volume 1 2 :=
          (continuous_id.pow 2).intervalIntegrable 1 2
        rw [intervalIntegral.integral_sub hl hq,intervalIntegral.integral_const_mul]
        norm_num
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((omissionDensity_continuous 0 .odd).intervalIntegrable (μ := volume) 0 1)
    ((omissionDensity_continuous 0 .odd).intervalIntegrable (μ := volume) 1 2)
  rw [hlow,hmid] at hsplit
  have hall := intervalIntegral.integral_Ioi_sub_Ioi (omissionDensity_integrable 0 .odd) (by norm_num : (0:ℝ)≤2)
  rw [hz,sub_zero] at hall
  unfold omissionLossTerm
  rw [he,zero_add]
  change (∫ y in Ioi 0,omissionDensity 0 .odd y)=1
  linarith

end ErdosContinuousOmission

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

noncomputable def freeGate (H : Profile) (i : Side) (r b : ℝ) : ℝ :=
  ∫ x in (1:ℝ)..baseCutoff b,H i.flip (r-x) x/(max 1 x)

theorem freeGate_continuous {H : Profile} (hH : JointContinuous H) : JointContinuous (freeGate H) := by
  intro i
  let F : (ℝ×ℝ) → ℝ → ℝ := fun p x => H i.flip (p.1-x) x/(max 1 x)
  have hc : Continuous (fun q : (ℝ×ℝ)×ℝ => H i.flip (q.1.1-q.2) q.2) :=
    (hH i.flip).comp ((continuous_fst.fst.sub continuous_snd).prodMk continuous_snd)
  have hd : Continuous (fun q : (ℝ×ℝ)×ℝ => max 1 q.2) := continuous_const.max continuous_snd
  have hF : Continuous F.uncurry := hc.div hd (fun q => ne_of_gt
    ((by norm_num : (0:ℝ)<1).trans_le (le_max_left 1 q.2)))
  have hb : Continuous (fun p : ℝ×ℝ => baseCutoff p.2) :=
    continuous_const.max (continuous_const.min continuous_snd)
  exact continuous_variable_upper_integral F hF (fun p => baseCutoff p.2) hb

theorem freeGate_nonnegative {H : Profile} (hH : ∀ i r b,0 ≤ H i r b) (i : Side) (r b : ℝ) :
    0 ≤ freeGate H i r b := by
  apply intervalIntegral.integral_nonneg_of_forall (baseCutoff_bounds b).1
  intro x
  exact div_nonneg (hH i.flip (r-x) x) (zero_le_one.trans (le_max_left 1 x))

theorem gate_le_freeGate {H : Profile} (hH : JointContinuous H)
    (hpos : ∀ i r b,0 ≤ H i r b) (i : Side) (r b : ℝ) : gate H i r b ≤ freeGate H i r b := by
  have hc := gate_integrand_continuous hH i r
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 1 (upperCutoff i r b))
    (hc.intervalIntegrable (μ := volume) (upperCutoff i r b) (baseCutoff b))
  have hp : 0 ≤ ∫ x in upperCutoff i r b..baseCutoff b,H i.flip (r-x) x/(max 1 x) := by
    apply intervalIntegral.integral_nonneg_of_forall (cutoff_le_base i r b)
    intro x
    exact div_nonneg (hpos i.flip (r-x) x) (zero_le_one.trans (le_max_left 1 x))
  unfold gate freeGate
  linarith

theorem gate_mono {H G : Profile} (hH : JointContinuous H) (hG : JointContinuous G)
    (h : ∀ i r b,H i r b ≤ G i r b) (i : Side) (r b : ℝ) : gate H i r b ≤ gate G i r b := by
  apply intervalIntegral.integral_mono_on (upperCutoff_bounds i r b).1
    ((gate_integrand_continuous hH i r).intervalIntegrable 1 _)
    ((gate_integrand_continuous hG i r).intervalIntegrable 1 _)
  intro x _
  exact div_le_div_of_nonneg_right (h i.flip (r-x) x) (zero_le_one.trans (le_max_left 1 x))

noncomputable def freeGateIterate : ℕ → Profile → Profile
  | 0,H => H
  | n+1,H => freeGate (freeGateIterate n H)

theorem freeGateIterate_continuous {H : Profile} (hH : JointContinuous H) (n : ℕ) :
    JointContinuous (freeGateIterate n H) := by
  induction n with
  | zero => exact hH
  | succ n ih => exact freeGate_continuous ih

theorem freeGateIterate_nonnegative {H : Profile} (hH : ∀ i r b,0 ≤ H i r b) (n : ℕ) :
    ∀ i r b,0 ≤ freeGateIterate n H i r b := by
  induction n with
  | zero => exact hH
  | succ n ih => exact freeGate_nonnegative ih

theorem gateIterate_prefix_le {H : Profile} (hH : JointContinuous H)
    (hpos : ∀ i r b,0 ≤ H i r b) (k n : ℕ) :
    ∀ i r b,gateIterate (k+n) H i r b ≤ freeGateIterate k (gateIterate n H) i r b := by
  induction k with
  | zero => intro i r b; simp only [zero_add,freeGateIterate,le_refl]
  | succ k ih =>
    intro i r b
    rw [show k+1+n=(k+n)+1 by omega,gateIterate,freeGateIterate]
    calc
      _ ≤ gate (freeGateIterate k (gateIterate n H)) i r b :=
        gate_mono (gateIterate_continuous hH _) (freeGateIterate_continuous (gateIterate_continuous hH n) k) ih i r b
      _ ≤ _ := gate_le_freeGate (freeGateIterate_continuous (gateIterate_continuous hH n) k)
        (freeGateIterate_nonnegative (gateIterate_nonnegative hpos n) k) i r b

theorem actual_omission_prefix_le (k : ℕ) (i : Side) (r b : ℝ) :
    gateIterate (k+2) omissionForce i r b ≤
      freeGateIterate k (gateIterate 2 omissionForce) i r b :=
  gateIterate_prefix_le omissionForce_continuous omissionForce_nonnegative k 2 i r b

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail

noncomputable def lastWindowCoefficient (S a b c : ℝ) : ℝ :=
  ((S+a+b+2*c)^3-(S+2*a)^3)/(12*c)

theorem last_window_integral (S a b c : ℝ) :
    (∫ y : ℝ in (S+2*a)/2..(S+a+b+2*c)/2,2*y^2/c)=lastWindowCoefficient S a b c := by
  rw [intervalIntegral.integral_div,intervalIntegral.integral_const_mul,integral_pow]
  norm_num
  unfold lastWindowCoefficient
  ring

theorem last_window_width {S a b c : ℝ} (ha : a ≤ 2) (hb : 1 ≤ b) (hc : 1 ≤ c) (hab : b ≤ a) :
    1 ≤ (S+a+b+2*c)-(S+2*a) ∧ (S+a+b+2*c)-(S+2*a) ≤ 2*c := by
  constructor <;> linarith

theorem last_window_square_bound {S a b c : ℝ} (hS : 0 ≤ S)
    (ha1 : 1 ≤ a) (ha2 : a ≤ 2) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c) (hab : b ≤ a) :
    lastWindowCoefficient S a b c ≤ (S+a+b+2*c)^2/2 := by
  have hw := last_window_width (S := S) ha2 hb1 hc1 hab
  have hU : 0 ≤ S+a+b+2*c := by linarith
  have hV : 0 ≤ S+2*a := by linarith
  have hUV : S+2*a ≤ S+a+b+2*c := by linarith
  have hcube : (S+a+b+2*c)^3-(S+2*a)^3 ≤
      3*(S+a+b+2*c)^2*((S+a+b+2*c)-(S+2*a)) := by
    have hp := mul_nonneg (sq_nonneg ((S+a+b+2*c)-(S+2*a))) (show 0 ≤ 2*(S+a+b+2*c)+(S+2*a) by linarith)
    nlinarith
  have hwidth := mul_le_mul_of_nonneg_left hw.2 (mul_nonneg (by norm_num : (0:ℝ)≤3) (sq_nonneg (S+a+b+2*c)))
  unfold lastWindowCoefficient
  apply (div_le_iff₀ (by linarith : 0 < 12*c)).mpr
  nlinarith

theorem last_window_mean_bound (k : ℕ) {S a b c : ℝ}
    (hSlo : (k:ℝ) ≤ S) (hShi : S ≤ 2*(k:ℝ)) (hSc : (k:ℝ)*c ≤ S)
    (ha1 : 1 ≤ a) (ha2 : a ≤ 2) (hb1 : 1 ≤ b) (hba : b ≤ a)
    (hc1 : 1 ≤ c) (hcb : c ≤ b) :
    lastWindowCoefficient S a b c ≤
      (((k:ℝ)+4)^2/2)*(3*(S+a+b+c)/((k:ℝ)+3)-2) := by
  let m : ℝ := (k:ℝ)+3
  let T : ℝ := S+a+b+c
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  have hm : 0 < m := by dsimp [m]; linarith
  have hTlo : m ≤ T := by dsimp [m,T]; linarith
  have hThi : T ≤ 2*m := by dsimp [m,T]; linarith
  have hTc : m*c ≤ T := by dsimp [m,T]; nlinarith
  have hmean1 : 1 ≤ T/m := (one_le_div hm).mpr hTlo
  have hmean2 : T/m ≤ 2 := (div_le_iff₀ hm).mpr hThi
  have hmean : (T/m)^2 ≤ 3*(T/m)-2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hmean1) (sub_nonneg.mpr hmean2)
    nlinarith
  have hA : S+a+b+2*c ≤ (m+1)*(T/m) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hm).mpr
    change (S+a+b+2*c)*m ≤ (m+1)*T
    dsimp [T] at hTc ⊢
    nlinarith
  have hA0 : 0 ≤ S+a+b+2*c := by linarith
  have hsq := mul_self_le_mul_self hA0 hA
  have hlin := mul_le_mul_of_nonneg_left hmean (sq_nonneg (m+1))
  have hw := last_window_square_bound (hSlo.trans' hk) ha1 ha2 hb1 hc1 hba
  have hme : (k:ℝ)+4=m+1 := by dsimp [m]; ring
  rw [hme]
  change lastWindowCoefficient S a b c ≤ ((m+1)^2/2)*(3*T/m-2)
  have hsq2 : (S+a+b+2*c)^2 ≤ (m+1)^2*(T/m)^2 := by nlinarith [hsq]
  calc
    _ ≤ (S+a+b+2*c)^2/2 := hw
    _ ≤ ((m+1)^2*(T/m)^2)/2 := div_le_div_of_nonneg_right hsq2 (by norm_num)
    _ ≤ ((m+1)^2*(3*(T/m)-2))/2 := div_le_div_of_nonneg_right hlin (by norm_num)
    _ = _ := by ring

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

noncomputable def orderedMass : ℕ → ℝ → ℝ
  | 0,_ => 1
  | n+1,b => ∫ x in (1:ℝ)..baseCutoff b,orderedMass n x/(max 1 x)

theorem orderedMass_continuous (n : ℕ) : Continuous (orderedMass n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous (fun x : ℝ => orderedMass n x/(max 1 x)) :=
      ih.div (continuous_const.max continuous_id) (fun x => ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)))
    exact (intervalIntegral.differentiable_integral_of_continuous hc).continuous.comp
      (continuous_const.max (continuous_const.min continuous_id))

theorem orderedMass_nonnegative (n : ℕ) (b : ℝ) : 0 ≤ orderedMass n b := by
  induction n generalizing b with
  | zero => norm_num [orderedMass]
  | succ n ih =>
    apply intervalIntegral.integral_nonneg_of_forall (baseCutoff_bounds b).1
    intro x
    exact div_nonneg (ih x) (zero_le_one.trans (le_max_left _ _))

theorem log_power_primitive (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (Real.log x)^(n+1)/((n+1).factorial:ℝ))
      ((Real.log x)^n/((n.factorial:ℝ)*x)) x := by
  have hh := ((Real.hasDerivAt_log hx.ne').pow (n+1)).div_const ((n+1).factorial:ℝ)
  convert! hh using 1
  simp only [Nat.add_sub_cancel_right,Nat.factorial_succ,Nat.cast_mul]
  have hn : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  field_simp

theorem orderedMass_eq (n : ℕ) {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    orderedMass n b=(Real.log b)^n/(n.factorial:ℝ) := by
  induction n generalizing b with
  | zero => norm_num [orderedMass]
  | succ n ih =>
    rw [orderedMass,baseCutoff_on hb1 hb2]
    have he : (∫ x in (1:ℝ)..b,orderedMass n x/(max 1 x))=
        ∫ x in (1:ℝ)..b,(Real.log x)^n/((n.factorial:ℝ)*x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb1] at hx
      dsimp only
      rw [ih hx.1 (hx.2.trans hb2),max_eq_right hx.1]
      ring
    rw [he]
    have hn : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hc : ContinuousOn (fun x : ℝ => (Real.log x)^n/((n.factorial:ℝ)*x)) (uIcc 1 b) := by
      rw [uIcc_of_le hb1]
      intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := simp_all)
    have hd : ∀ x ∈ uIcc (1:ℝ) b,HasDerivAt
        (fun x : ℝ => (Real.log x)^(n+1)/((n+1).factorial:ℝ))
        ((Real.log x)^n/((n.factorial:ℝ)*x)) x := by
      intro x hx
      rw [uIcc_of_le hb1] at hx
      exact log_power_primitive n (by linarith [hx.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable (μ := volume))]
    simp

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

abbrev ScalarProfile := ℝ → ℝ → ℝ
def ScalarContinuous (H : ScalarProfile) : Prop := Continuous (fun p : ℝ×ℝ => H p.1 p.2)
noncomputable def scalarFreeGate (H : ScalarProfile) (r b : ℝ) : ℝ :=
  ∫ x in (1:ℝ)..baseCutoff b,H (r-x) x/(max 1 x)

noncomputable def scalarFreeIterate : ℕ → ScalarProfile → ScalarProfile
  | 0,H => H
  | n+1,H => scalarFreeGate (scalarFreeIterate n H)

theorem scalarFreeGate_continuous {H : ScalarProfile} (hH : ScalarContinuous H) :
    ScalarContinuous (scalarFreeGate H) :=
  freeGate_continuous (H := fun _ => H) (fun _ => hH) .even

theorem scalarFreeIterate_continuous {H : ScalarProfile} (hH : ScalarContinuous H) (n : ℕ) :
    ScalarContinuous (scalarFreeIterate n H) := by
  induction n with
  | zero => exact hH
  | succ n ih => exact scalarFreeGate_continuous ih

theorem freeGate_total {H : Profile} (hH : JointContinuous H) (r b : ℝ) :
    freeGate H .even r b+freeGate H .odd r b=
      scalarFreeGate (fun r b => H .even r b+H .odd r b) r b := by
  have he := (gate_integrand_continuous hH .even r).intervalIntegrable (μ := volume) 1 (baseCutoff b)
  have ho := (gate_integrand_continuous hH .odd r).intervalIntegrable (μ := volume) 1 (baseCutoff b)
  unfold freeGate scalarFreeGate
  rw [← intervalIntegral.integral_add he ho]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only [Side.flip]
  ring

theorem freeGateIterate_total {H : Profile} (hH : JointContinuous H) (n : ℕ) (r b : ℝ) :
    freeGateIterate n H .even r b+freeGateIterate n H .odd r b=
      scalarFreeIterate n (fun r b => H .even r b+H .odd r b) r b := by
  induction n generalizing r b with
  | zero => rfl
  | succ n ih =>
    rw [freeGateIterate,freeGate_total (freeGateIterate_continuous hH n)]
    have he : (fun r b => freeGateIterate n H .even r b+freeGateIterate n H .odd r b)=
        scalarFreeIterate n (fun r b => H .even r b+H .odd r b) := by funext r b; exact ih r b
    rw [he]
    rfl

noncomputable def terminalBlock (r b : ℝ) : ℝ := gateIterate 2 omissionForce .odd r b

theorem terminalBlock_continuous : ScalarContinuous terminalBlock :=
  gateIterate_continuous omissionForce_continuous 2 .odd

theorem terminalBlock_nonnegative (r b : ℝ) : 0 ≤ terminalBlock r b :=
  gateIterate_nonnegative omissionForce_nonnegative 2 .odd r b

theorem actual_free_total (k : ℕ) (r b : ℝ) :
    freeGateIterate k (gateIterate 2 omissionForce) .even r b+
      freeGateIterate k (gateIterate 2 omissionForce) .odd r b=
        scalarFreeIterate k terminalBlock r b := by
  rw [freeGateIterate_total (gateIterate_continuous omissionForce_continuous 2)]
  have he : (fun r b => gateIterate 2 omissionForce .even r b+gateIterate 2 omissionForce .odd r b)=terminalBlock := by
    funext r b
    have hh := (omission_wrong_parity_zero 1).1 r b
    norm_num only [Nat.reduceMul] at hh
    rw [hh,zero_add]
    rfl
  rw [he]

noncomputable def combinedDensity (n : ℕ) (y : ℝ) : ℝ :=
  (if 1 < y then omissionDensity n .even y else 0)+omissionDensity n .odd y

theorem actual_combined_density_le (k : ℕ) (y : ℝ) :
    combinedDensity (k+2) y ≤ 2*y^2*scalarFreeIterate k terminalBlock (2*y+2) 2 := by
  have he := actual_omission_prefix_le k .even (2*y+2) 2
  have ho := actual_omission_prefix_le k .odd (2*y+2) 2
  have hpe := gateIterate_nonnegative omissionForce_nonnegative (k+2) .even (2*y+2) 2
  have hfE := freeGateIterate_nonnegative (gateIterate_nonnegative omissionForce_nonnegative 2) k .even (2*y+2) 2
  have hbE : (if 1 < y then omissionDensity (k+2) .even y else 0) ≤
      2*y^2*freeGateIterate k (gateIterate 2 omissionForce) .even (2*y+2) 2 := by
    by_cases h : 1 < y
    · rw [ite_eq_left h]
      have hh := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg y))
      unfold omissionDensity sourceWeight
      nlinarith
    · rw [ite_eq_right h]
      exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg y)) hfE
  have hbO : omissionDensity (k+2) .odd y ≤
      2*y^2*freeGateIterate k (gateIterate 2 omissionForce) .odd (2*y+2) 2 :=
    mul_le_mul_of_nonneg_left ho (mul_nonneg (by norm_num) (sq_nonneg y))
  have hh := actual_free_total k (2*y+2) 2
  unfold combinedDensity
  nlinarith

end ErdosOmissionTail

end

end Erdos970

end OAI
