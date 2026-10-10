import OAI.NumberTheory.Jacobsthal.Analysis.ScalarMassContinuity
import OAI.NumberTheory.Jacobsthal.Analysis.SourceReferenceLimit
import OAI.NumberTheory.Jacobsthal.Analysis.ThirdMovingIntegrals
import OAI.NumberTheory.Jacobsthal.Probability.OrderedWindowKernel
import OAI.NumberTheory.Jacobsthal.Sieve.ExponentialTailBound

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosBoundaryLoss

theorem thirdInner_integral {x u : ℝ} (hx : x ∈ Icc (1:ℝ) 2) (hu : u ∈ Icc (1:ℝ) x) :
    (2/x)*(∫ y in Icc x 4,thirdInnerKernel x (y,u))=
      ∫ t : ℝ in 1..u,loss3Kernel t u x := by
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have hu2 : u ≤ 2 := hu.2.trans hx.2
  have h := integrated_force_window (x+u) x 4 u 0 (by linarith [hx.1]) hu.1 hu2
    (by linarith [hx.2,hu.1]) (by linarith [hx.2])
  have he : (fun y : ℝ => thirdInnerKernel x (y,u))=
      (fun y => u⁻¹*(y^2*omissionForce .odd (2*y+2-(x+u)) u)) := by
    funext y
    have hh : 2*y+2-x-u=2*y+2-(x+u) := by ring
    simp only [thirdInnerKernel,max_eq_right hu.1,hh]
    ring
  rw [he,integral_const_mul,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hx.2] : x≤4)]
  simp only [sub_zero,zero_mul,sub_zero] at h
  rw [h,← mul_assoc,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hu.1] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  dsimp only [loss3Kernel]
  field_simp
  ring

theorem thirdKernel_integral {x : ℝ} (hx : x ∈ Icc (1:ℝ) 2) :
    (∫ y in Icc (0:ℝ) 4,thirdKernel (y,x))=
      ∫ u : ℝ in 1..x,∫ t : ℝ in 1..u,loss3Kernel t u x := by
  classical
  have he : (fun y : ℝ => thirdKernel (y,x))=
      (Ici x).indicator (fun y => (2/x)*(y^2*gate omissionForce .even (2*y+2-x) x)) := by
    funext y
    dsimp only [thirdKernel]
    by_cases hh : x≤y
    · rw [ite_eq_left hh,indicator_of_mem (show y ∈ Ici x from hh),max_eq_right hx.1]
      ring
    · rw [ite_eq_right hh,indicator_of_notMem (show y ∉ Ici x from hh)]
  have hset : Icc (0:ℝ) 4 ∩ Ici x=Icc x 4 := by
    ext y
    constructor
    · rintro ⟨hy,hxy⟩; exact ⟨hxy,hy.2⟩
    · intro hy; exact ⟨⟨by linarith [hx.1,hy.1],hy.2⟩,hy.1⟩
  rw [he,setIntegral_indicator measurableSet_Ici,hset,integral_const_mul]
  simp_rw [third_even_gate _ hx,intervalIntegral.integral_of_le hx.1,← integral_Icc_eq_integral_Ioc]
  rw [bounded_rectangle_swap (thirdInnerKernel_continuous x).measurable x 4 1 x 16
    (fun _ hy _ hu => thirdInnerKernel_bound hx hy hu),← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  exact thirdInner_integral hx hu

theorem third_loss_ordered_integral :
    omissionLossTerm 2=∫ x : ℝ in 1..2,∫ u : ℝ in 1..x,∫ t : ℝ in 1..u,loss3Kernel t u x := by
  rw [third_loss_bounded]
  simp_rw [third_density_kernel]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤4)]
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2),← integral_Icc_eq_integral_Ioc]
  rw [bounded_rectangle_swap thirdKernel_measurable 0 4 1 2 32
    (fun _ hy _ hx => thirdKernel_bound hy hx)]
  exact setIntegral_congr_fun measurableSet_Icc (fun _ hx => thirdKernel_integral hx)

end ErdosOmissionBindings

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosBoundaryLoss

theorem third_inner_rectangle_swap {u : ℝ} (hu : u ∈ Icc (1:ℝ) 2) :
    (∫ x : ℝ in u..2,∫ t : ℝ in 1..u,loss3Kernel t u x)=
      ∫ t : ℝ in 1..u,∫ x : ℝ in u..2,loss3Kernel t u x := by
  have hm : Measurable (fun p : ℝ×ℝ => loss3Kernel p.2 u p.1) := by unfold loss3Kernel; fun_prop
  have hb : ∀ x ∈ Icc u 2,∀ t ∈ Icc (1:ℝ) u,|loss3Kernel t u x| ≤ 64 := by
    intro x hx t ht
    exact lossThree_bound ⟨hu.1.trans hx.1,hx.2⟩ hu ⟨ht.1,ht.2.trans hu.2⟩
  have h := bounded_rectangle_swap hm u 2 1 u 64 hb
  simpa only [intervalIntegral.integral_of_le hu.1,intervalIntegral.integral_of_le hu.2,
    ← integral_Icc_eq_integral_Ioc] using h

theorem third_ordered_reversal :
    (∫ x : ℝ in 1..2,∫ u : ℝ in 1..x,∫ t : ℝ in 1..u,loss3Kernel t u x)=L3 := by
  calc
    _ = ∫ x : ℝ in 1..2,∫ u : ℝ in 1..x,thirdLowerIntegral (x,u) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hx
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hx.1] at hu
      exact (thirdLowerIntegral_eq hx ⟨hu.1,hu.2.trans hx.2⟩).symm
    _ = ∫ u : ℝ in 1..2,∫ x : ℝ in u..2,thirdLowerIntegral (x,u) :=
      ordered_triangle_swap thirdLowerIntegral_continuous.measurable (by norm_num : (0:ℝ)≤64)
        (fun _ _ _ _ => thirdLowerIntegral_bound _)
    _ = ∫ u : ℝ in 1..2,∫ t : ℝ in 1..u,∫ x : ℝ in u..2,loss3Kernel t u x := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hu
      have he : (∫ x : ℝ in u..2,thirdLowerIntegral (x,u))=
          ∫ x : ℝ in u..2,∫ t : ℝ in 1..u,loss3Kernel t u x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hu.2] at hx
        exact thirdLowerIntegral_eq ⟨hu.1.trans hx.1,hx.2⟩ hu
      exact he.trans (third_inner_rectangle_swap hu)
    _ = ∫ u : ℝ in 1..2,∫ t : ℝ in 1..u,thirdUpperIntegral (u,t) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hu
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hu.1] at ht
      exact (thirdUpperIntegral_eq hu ⟨ht.1,ht.2.trans hu.2⟩).symm
    _ = ∫ t : ℝ in 1..2,∫ u : ℝ in t..2,thirdUpperIntegral (u,t) :=
      ordered_triangle_swap thirdUpperIntegral_continuous.measurable (by norm_num : (0:ℝ)≤64)
        (fun _ _ _ _ => thirdUpperIntegral_bound _)
    _ = L3 := by
      unfold L3
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at ht
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.2] at hu
      exact thirdUpperIntegral_eq ⟨ht.1.trans hu.1,hu.2⟩ ht

theorem actual_third_loss_eq_L3 : omissionLossTerm 2=L3 :=
  third_loss_ordered_integral.trans third_ordered_reversal

end ErdosOmissionBindings

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

theorem terminal_mass_affine_bound (k : ℕ) {S b : ℝ}
    (hSlo : (k:ℝ) ≤ S) (hShi : S ≤ 2*(k:ℝ)) (hSb : (k:ℝ)*b ≤ S)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass 0 S b ≤ (((k:ℝ)+4)^2/2)*orderedAffine ((k:ℝ)+3) 3 S b := by
  let m : ℝ := (k:ℝ)+3
  let C : ℝ := ((k:ℝ)+4)^2/2
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  have hS : 0 ≤ S := hk.trans hSlo
  have hmiddle : ∀ a ∈ Icc (1:ℝ) b,∀ u ∈ Icc (1:ℝ) a,
      windowMiddle S a u ≤ C/(a*u)*orderedAffine m 1 (S+a+u) u := by
    intro a ha u hu
    have ha2 : a ≤ 2 := ha.2.trans hb2
    have hu2 : u ≤ 2 := hu.2.trans ha2
    have ha0 : 0 < a := by linarith [ha.1]
    have hu0 : 0 < u := by linarith [hu.1]
    have hpmap : Continuous (fun c : ℝ => ((a,u),c)) := by fun_prop
    have hlower : Continuous (windowKernel S a u) := by
      simpa only [Function.comp_def] using! (windowKernel_continuous S).comp hpmap
    have hupper := (orderedAffine_shift_div_continuous m 0 (S+a+u)).const_mul (C/(a*u))
    have hh := intervalIntegral.integral_mono_on hu.1
      (hlower.intervalIntegrable (μ := volume) 1 u) (hupper.intervalIntegrable (μ := volume) 1 u) (fun c hc => by
        have hc0 : 0 < c := by linarith [hc.1]
        have hcb : c ≤ b := hc.2.trans (hu.2.trans ha.2)
        have hSc : (k:ℝ)*c ≤ S := (mul_le_mul_of_nonneg_left hcb hk).trans hSb
        have hw := last_window_mean_bound k hSlo hShi hSc ha.1 ha2 hu.1 hu.2 hc.1 hc.2
        rw [windowKernel_literal ha.1 hu.1 hc.1]
        change lastWindowCoefficient S a u c/(a*u*c) ≤ C/(a*u)*(orderedAffine m 0 (S+a+u+c) c/(max 1 c))
        rw [orderedAffine_zero,max_eq_right hc.1]
        have hd := div_le_div_of_nonneg_right hw (show 0 ≤ a*u*c by positivity)
        convert! hd using 1; dsimp [C,m]; ring)
    unfold windowMiddle
    rw [baseCutoff_on hu.1 hu2]
    apply hh.trans_eq
    rw [intervalIntegral.integral_const_mul,orderedAffine_succ m 0 (S+a+u) u,baseCutoff_on hu.1 hu2]
  have houter : ∀ a ∈ Icc (1:ℝ) b,windowOuter S a ≤ C/a*orderedAffine m 2 (S+a) a := by
    intro a ha
    have ha2 : a ≤ 2 := ha.2.trans hb2
    have hpmap : Continuous (fun u : ℝ => (a,u)) := by fun_prop
    have hlower : Continuous (windowMiddle S a) := by
      simpa only [Function.comp_def] using! (windowMiddle_continuous S).comp hpmap
    have hupper := (orderedAffine_shift_div_continuous m 1 (S+a)).const_mul (C/a)
    have hh := intervalIntegral.integral_mono_on ha.1
      (hlower.intervalIntegrable (μ := volume) 1 a) (hupper.intervalIntegrable (μ := volume) 1 a) (fun u hu => by
        have hw := hmiddle a ha u hu
        change windowMiddle S a u ≤ C/a*(orderedAffine m 1 (S+a+u) u/(max 1 u))
        rw [max_eq_right hu.1]
        convert! hw using 1; ring)
    unfold windowOuter
    rw [baseCutoff_on ha.1 ha2]
    apply hh.trans_eq
    rw [intervalIntegral.integral_const_mul,orderedAffine_succ m 1 (S+a) a,baseCutoff_on ha.1 ha2]
  rw [scalarTailMass_zero_eq_windowMass hS hb1 hb2,windowMass,baseCutoff_on hb1 hb2]
  have hupper := (orderedAffine_shift_div_continuous m 2 S).const_mul C
  have hh := intervalIntegral.integral_mono_on hb1
    ((windowOuter_continuous S).intervalIntegrable (μ := volume) 1 b)
    (hupper.intervalIntegrable (μ := volume) 1 b) (fun a ha => by
      have hw := houter a ha
      change windowOuter S a ≤ C*(orderedAffine m 2 (S+a) a/(max 1 a))
      rw [max_eq_right ha.1]
      convert! hw using 1; ring)
  apply hh.trans_eq
  rw [intervalIntegral.integral_const_mul,orderedAffine_succ m 2 S b,baseCutoff_on hb1 hb2]

end ErdosOmissionTail

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosBoundaryLoss

theorem actual_second_loss_value : omissionLossTerm 1=-(35:ℝ)/36-(Real.log 2)^2+3*Real.log 2 :=
  actual_second_loss_eq_L2.trans L2_eq

theorem actual_third_loss_value : omissionLossTerm 2=(623:ℝ)/432-(19:ℝ)/12*Real.log 2+(1:ℝ)/3*(Real.log 2)^2 :=
  actual_third_loss_eq_L3.trans L3_eq

theorem actual_first_three_loss_lt : omissionLossTerm 0+omissionLossTerm 1+omissionLossTerm 2<(43:ℝ)/20 := by
  rw [actual_first_loss_eq_one,actual_second_loss_eq_L2,actual_third_loss_eq_L3]
  linarith [L2_lt,L3_lt]

theorem actual_first_three_partial_sum_lt : (∑ n ∈ Finset.range 3,omissionLossTerm n)<(43:ℝ)/20 := by
  have h := actual_first_three_loss_lt
  simpa only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add] using h

end ErdosOmissionBindings

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

theorem scalarTailMass_affine_bound (n k : ℕ) {S b : ℝ}
    (hSlo : (k:ℝ) ≤ S) (hShi : S ≤ 2*(k:ℝ)) (hSb : (k:ℝ)*b ≤ S)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass n S b ≤ (((k:ℝ)+(n:ℝ)+4)^2/2)*
      orderedAffine ((k:ℝ)+(n:ℝ)+3) (n+3) S b := by
  induction n generalizing k S b with
  | zero =>
    simpa only [Nat.cast_zero,add_zero,Nat.zero_add] using terminal_mass_affine_bound k hSlo hShi hSb hb1 hb2
  | succ n ih =>
    have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    have hS : 0 ≤ S := hk.trans hSlo
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show (k:ℝ)+((n:ℝ)+1)+4=(k:ℝ)+(n:ℝ)+5 by ring,
      show (k:ℝ)+((n:ℝ)+1)+3=(k:ℝ)+(n:ℝ)+4 by ring,
      show (n+1)+3=(n+3)+1 by omega]
    let m : ℝ := (k:ℝ)+(n:ℝ)+4
    let C : ℝ := ((k:ℝ)+(n:ℝ)+5)^2/2
    change scalarTailMass (n+1) S b ≤ C*orderedAffine m ((n+3)+1) S b
    rw [scalarTailMass_succ n hS hb1 hb2,orderedAffine_succ,baseCutoff_on hb1 hb2,
      ← intervalIntegral.integral_const_mul]
    have hpmap : Continuous (fun x : ℝ => (S+x,x)) := by fun_prop
    have hc : Continuous (fun x : ℝ => scalarTailMass n (S+x) x/(max 1 x)) :=
      ((scalarTailMass_continuous n).comp hpmap).div (continuous_const.max continuous_id)
        (fun x => ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)))
    have hlow : IntervalIntegrable (fun x : ℝ => scalarTailMass n (S+x) x/x) volume 1 b := by
      apply (hc.intervalIntegrable (μ := volume) 1 b).congr_uIoo
      intro x hx
      rw [uIoo_of_le hb1] at hx
      simp only [max_eq_right hx.1.le]
    have hupper := (orderedAffine_shift_div_continuous m (n+3) S).const_mul C
    apply intervalIntegral.integral_mono_on hb1 hlow (hupper.intervalIntegrable (μ := volume) 1 b)
    intro x hx
    have hx2 : x ≤ 2 := hx.2.trans hb2
    have hlo : ((k+1:ℕ):ℝ) ≤ S+x := by push_cast; linarith [hx.1]
    have hhi : S+x ≤ 2*((k+1:ℕ):ℝ) := by push_cast; linarith
    have horder : ((k+1:ℕ):ℝ)*x ≤ S+x := by
      have hh := mul_le_mul_of_nonneg_left hx.2 hk
      push_cast
      nlinarith
    have hh := ih (k+1) hlo hhi horder hx.1 hx2
    have hm : ((k+1:ℕ):ℝ)+(n:ℝ)+3=m := by dsimp [m]; push_cast; ring
    have hC : (((k+1:ℕ):ℝ)+(n:ℝ)+4)^2/2=C := by dsimp [C]; push_cast; ring
    rw [hm,hC] at hh
    rw [max_eq_right hx.1]
    have hd := div_le_div_of_nonneg_right hh (show 0 ≤ x by linarith [hx.1])
    convert! hd using 1; ring

end ErdosOmissionTail

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

theorem actual_omission_factorial_bound (n : ℕ) :
    omissionLossTerm (n+3) ≤
      (1:ℝ)/2*(3/Real.log 2-2)*weightedExpTerm (Real.log 2) (n+4) := by
  have hh := scalarTailMass_affine_bound (n+1) 0 (S := 0) (b := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl
  norm_num only [Nat.cast_zero,zero_add] at hh
  have hm : ((n+1:ℕ):ℝ)+3=((n+4:ℕ):ℝ) := by push_cast; ring
  rw [hm,show (n+1)+3=n+4 by omega,show n+4=(n+3)+1 by omega,orderedAffine_at_two] at hh
  have hc := (actual_loss_le_scalarTailMass (n+1)).trans hh
  have he : (n+1)+2=n+3 := by omega
  rw [he] at hc
  convert! hc using 1
  unfold weightedExpTerm expTerm
  push_cast
  ring

theorem actual_omission_tail_lt : (∑' n : ℕ,omissionLossTerm (n+3)) < (37:ℝ)/100 := by
  have hl : Summable (fun n : ℕ => omissionLossTerm (n+3)) :=
    actual_loss_summable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hu := weighted_log_two_tail_hasSum.summable.mul_left ((1:ℝ)/2*(3/Real.log 2-2))
  have hh := hl.tsum_le_tsum actual_omission_factorial_bound hu
  rw [tsum_mul_left] at hh
  exact hh.trans_lt numerical_tail_majorant_lt

theorem actual_omission_tail_indicator_lt :
    (∑' n : ℕ,if 3 ≤ n then omissionLossTerm n else 0) < (37:ℝ)/100 := by
  have hl : Summable (fun n : ℕ => omissionLossTerm (n+3)) :=
    actual_loss_summable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hg : HasSum (fun n : ℕ => if 3 ≤ n then omissionLossTerm n else 0)
      (∑' n : ℕ,omissionLossTerm (n+3)) := by
    apply (hasSum_nat_add_iff' 3).mp
    have heval (n : ℕ) : (if 3 ≤ n+3 then omissionLossTerm (n+3) else 0)=omissionLossTerm (n+3) :=
      ite_eq_left (by omega)
    simp_rw [heval]
    simpa only [Finset.sum_range_succ,Finset.sum_range_zero,Finset.sum_empty,
      show ¬3 ≤ 0 by omega,show ¬3 ≤ 1 by omega,show ¬3 ≤ 2 by omega,ite_false,add_zero,sub_zero] using hl.hasSum
  have he := hg.tsum_eq
  rw [he]
  exact actual_omission_tail_lt

end ErdosOmissionTail

end

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosPositiveReference
open ErdosOmissionBindings ErdosOmissionTail ErdosContinuousOmission
open ErdosBoundaryIntegral ErdosBoundaryLoss
open Erdos970Dependency.InvariantCostBound
open NumberTheoryLean.BuchstabBridge

theorem actual_I_gt_eleven_seventyfive : (11:ℝ)/75 < signedCoefficientI := by
  have hfirst := actual_first_three_partial_sum_lt
  have htail := actual_omission_tail_lt
  have hsplit := actual_loss_summable.sum_add_tsum_nat_add 3
  have htotal := actual_signed_loss_series
  linarith

theorem actual_I_gt_source_margin : (14:ℝ)/100 < signedCoefficientI := by
  linarith [actual_I_gt_eleven_seventyfive]

theorem exp_gamma_lt_two : Real.exp Real.eulerMascheroniConstant < 2 := by
  have hg : Real.eulerMascheroniConstant < Real.log 2 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds,log_two_bounds.1]
  have h := Real.exp_lt_exp.mpr hg
  simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using h

theorem costMass_lt_eight : costMass < 8 := by
  have h := costMass_le
  change costMass ≤ 2*(2*Real.exp Real.eulerMascheroniConstant) at h
  linarith [exp_gamma_lt_two]

theorem source_reference_coefficient_margin :
    (2:ℝ)/100 < -(1:ℝ)/100+2*signedCoefficientI/costMass := by
  have h : (3:ℝ)/100 < 2*signedCoefficientI/costMass := by
    apply (lt_div_iff₀ costMass_pos).mpr
    nlinarith [actual_I_gt_eleven_seventyfive,costMass_lt_eight]
  linarith

end ErdosPositiveReference

end

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosSourceReferenceMargin
open ErdosCorrectionLimit ErdosBoundaryIntegral ErdosPositiveReference
open NumberTheoryLean.ReferenceSourceDecomposition
open Erdos970Dependency.InvariantCostBound

theorem actual_reference_limit_positive :
    Real.exp Real.eulerMascheroniConstant/100 <
      Real.exp Real.eulerMascheroniConstant*(-(1:ℝ)/100+2*signedCoefficientI/costMass) := by
  have hh := mul_lt_mul_of_pos_left source_reference_coefficient_margin (Real.exp_pos Real.eulerMascheroniConstant)
  nlinarith [Real.exp_pos Real.eulerMascheroniConstant]

theorem actual_source_reference_lower_bound :
    ∃ c_L z₀ : ℝ,0 < c_L ∧ 1 < z₀ ∧ ∀ z : ℝ,z₀ ≤ z →
      c_L ≤ (ErdosInverseBoxHeight.sourceB z)^2*
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) ∧
      c_L/(ErdosInverseBoxHeight.sourceB z)^2 ≤
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) := by
  let c_L : ℝ := Real.exp Real.eulerMascheroniConstant/100
  have hc : 0 < c_L := div_pos (Real.exp_pos _) (by norm_num)
  have hevent := actual_sourceReference_tendsto.eventually (Ioi_mem_nhds actual_reference_limit_positive)
  have he : ∀ᶠ z : ℝ in atTop,
      c_L ≤ (ErdosInverseBoxHeight.sourceB z)^2*
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) ∧
      c_L/(ErdosInverseBoxHeight.sourceB z)^2 ≤
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) := by
    filter_upwards [hevent,rootB_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with z hz hB
    have hz' : c_L < (ErdosInverseBoxHeight.sourceB z)^2*
        sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) := hz
    refine ⟨hz'.le,?_⟩
    apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr
    simpa only [mul_comm] using hz'.le
  obtain ⟨z₁,hz₁⟩ := eventually_atTop.mp he
  refine ⟨c_L,max 2 z₁,hc,by have h := le_max_left (2:ℝ) z₁; linarith,?_⟩
  intro z hz
  exact hz₁ z ((le_max_right _ _).trans hz)

theorem actual_source_reference_eventually_positive :
    ∃ z₀ : ℝ,1 < z₀ ∧ ∀ z : ℝ,z₀ ≤ z →
      0 < sourceReference (ErdosInverseBoxHeight.sourceW z) (sourceRootNode (1/100) z) := by
  obtain ⟨c_L,z₁,hc,hz₁,h⟩ := actual_source_reference_lower_bound
  obtain ⟨z₂,hz₂⟩ := eventually_atTop.mp (rootB_tendsto.eventually (eventually_gt_atTop (0:ℝ)))
  refine ⟨max z₁ z₂,hz₁.trans_le (le_max_left _ _),?_⟩
  intro z hz
  have hB := hz₂ z ((le_max_right _ _).trans hz)
  exact (div_pos hc (sq_pos_of_pos hB)).trans_le (h z ((le_max_left _ _).trans hz)).2

end ErdosSourceReferenceMargin

end


namespace NumberTheoryLean.SourceRootReference
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership
open ReferenceSourceDecomposition ReferenceSourcePrimeSets ReferenceProductsBasics ReferenceAdmission
open LogarithmicBinPartition SourceNodeCoordinates
open ErdosCorrectionLimit ErdosSourceReferenceMargin ErdosInverseBoxHeight
open scoped Topology


theorem source_primes_eq_root_set {top : ℝ} (htop : 1 < top) (hw : 1 < sourceW top) :
    sourcePrimes (sourceW top) (sourceB top) true=sourcePrimeSet (sourceW top) top := by
  have hp : (sourceW top)^(sourceB top)=top :=
    (JacobsthalSourceScale.sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans htop))
  rw [sourcePrimes,hp,availablePrimes_closed,primesBetween_eq_sdiff (zero_lt_one.trans hw).le]
  rfl

theorem source_reference_root_polynomial (a top : ℝ) (htop : 1 < top) (hw : 1 < sourceW top) :
    sourceReference (sourceW top) (sourceRootNode a top)=
      referencePolynomial (sourceW top) (sourcePrimeSet (sourceW top) top)
        (sourceRootNode a top).side (sourceRootNode a top).gap := by
  unfold sourceReference
  change referencePolynomial _ (sourcePrimes (sourceW top) (sourceB top) true) _ _=_
  rw [source_primes_eq_root_set htop hw]

theorem source_root_polynomial_margin : ∃ c_L : ℝ,0 < c_L ∧ ∀ᶠ top : ℝ in atTop,
    c_L ≤ (sourceB top)^2*referencePolynomial (sourceW top) (sourcePrimeSet (sourceW top) top)
      (sourceRootNode (1/100) top).side (sourceRootNode (1/100) top).gap := by
  obtain ⟨c_L,T,hc,_hT,hMargin⟩ := actual_source_reference_lower_bound
  refine ⟨c_L,hc,?_⟩
  filter_upwards [eventually_ge_atTop T,actual_root_eventually (1/100),eventually_gt_atTop (1:ℝ)] with top htop hroot ht1
  have hh := (hMargin top htop).1
  rwa [source_reference_root_polynomial (1/100) top ht1 hroot.2.1] at hh

theorem source_root_eventually_data : ∀ᶠ top : ℝ in atTop,
    0 < sourceY top ∧ 3 ≤ sourceB top ∧ 1 < sourceW top ∧ sourceW top < top ∧
    Real.log (sourceB top) ≤ 2*Real.log (sourceW top) ∧
    199/100 ≤ (sourceRootNode (1/100) top).ratio ∧ (sourceRootNode (1/100) top).ratio ≤ 23/10 ∧
    Consistent (sourceRootNode (1/100) top) ∧ (sourceW top)^(sourceB top)=top := by
  filter_upwards [actual_root_eventually (1/100),rootB_tendsto.eventually_ge_atTop 3,
    Real.tendsto_log_atTop.eventually JacobsthalSourceScale.sourceW_bounds_eventually,eventually_gt_atTop (1:ℝ)]
    with top hroot hB hW ht1
  obtain ⟨_hBpos,hw,hcomp,h199,h23,_hgap,hcons⟩ := hroot
  have hwt : sourceW top < top := by
    have hsmall : sourceW top ≤ Real.log top := hW.2.2
    have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans ht1)
    linarith
  have hY : 0 < sourceY top := by
    by_contra! hn
    have hzero : sourceY top=0 := by omega
    have hg : (sourceRootNode (1/100) top).gap=199/100 := by
      change Real.log (sourceY top:ℝ)/Real.log (sourceW top)-(1:ℝ)/100+2=199/100
      rw [hzero]
      norm_num
    have hs : Valid (sourceRootNode (1/100) top).side (sourceRootNode (1/100) top).ratio := by
      change 198/100 ≤ (sourceRootNode (1/100) top).ratio
      linarith
    have he := node_gap_eq hs hcons (rfl : (sourceRootNode (1/100) top).cutoff=sourceB top)
    change (sourceRootNode (1/100) top).gap=sourceB top*(sourceRootNode (1/100) top).ratio at he
    have hprod := mul_le_mul h199 hB (by norm_num : (0:ℝ)≤3) (by linarith : 0 ≤ (sourceRootNode (1/100) top).ratio)
    nlinarith
  exact ⟨hY,hB,hw,hwt,hcomp,h199,h23,hcons,
    (JacobsthalSourceScale.sourceW_pow_sourceB hw).trans (Real.exp_log (zero_lt_one.trans ht1))⟩
end NumberTheoryLean.SourceRootReference


end Erdos970

end OAI
