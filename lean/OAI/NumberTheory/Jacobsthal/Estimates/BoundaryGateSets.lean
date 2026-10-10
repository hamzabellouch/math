import OAI.NumberTheory.Jacobsthal.Analysis.IntegralDifferenceBound
import OAI.NumberTheory.Jacobsthal.Analysis.VariableUpperIntegral
import OAI.NumberTheory.Jacobsthal.Estimates.ReferenceWeightedQuadrature

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

noncomputable def boundaryTerm : ℕ → Side → ℝ → ℝ → ℝ
  | 0,_,_,_ => 1
  | n+1,i,r,b => ∫ x in (1:ℝ)..upperCutoff i r b,boundaryTerm n i.flip (r-x) x/(max 1 x)

theorem boundaryTerm_continuous (n : ℕ) (i : Side) :
    Continuous (fun p : ℝ×ℝ => boundaryTerm n i p.1 p.2) := by
  induction n generalizing i with
  | zero => exact continuous_const
  | succ n ih =>
    let F : (ℝ×ℝ) → ℝ → ℝ := fun p x => boundaryTerm n i.flip (p.1-x) x/(max 1 x)
    have hchild : Continuous (fun q : (ℝ×ℝ)×ℝ => boundaryTerm n i.flip (q.1.1-q.2) q.2) :=
      (ih i.flip).comp ((continuous_fst.fst.sub continuous_snd).prodMk continuous_snd)
    have hden : Continuous (fun q : (ℝ×ℝ)×ℝ => (max 1 q.2)⁻¹) :=
      (continuous_const.max continuous_snd).inv₀ (fun q => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left 1 q.2)))
    have hF : Continuous F.uncurry := by
      have he : F.uncurry = (fun q : (ℝ×ℝ)×ℝ => boundaryTerm n i.flip (q.1.1-q.2) q.2) *
          (fun q => (max 1 q.2)⁻¹) := by
        funext ⟨p,x⟩
        exact div_eq_mul_inv _ _
      rw [he]
      exact hchild.mul hden
    exact continuous_variable_upper_integral F hF (fun p => upperCutoff i p.1 p.2) (upperCutoff_continuous i)

theorem boundaryTerm_reciprocal (n : ℕ) (i : Side) (r b : ℝ) :
    boundaryTerm (n+1) i r b =
      ∫ x in (1:ℝ)..upperCutoff i r b,boundaryTerm n i.flip (r-x) x/x := by
  change (∫ x in (1:ℝ)..upperCutoff i r b,boundaryTerm n i.flip (r-x) x/(max 1 x)) = _
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
  dsimp only
  rw [max_eq_right hx.1]

theorem boundaryTerm_low (n : ℕ) (i : Side) (r b : ℝ) (hb : b ≤ 1) :
    boundaryTerm (n+1) i r b=0 := by
  rw [boundaryTerm,upperCutoff_low hb,intervalIntegral.integral_same]

theorem boundaryTerm_odd_small (n : ℕ) {r b : ℝ} (hr : r ≤ 4) :
    boundaryTerm (n+1) .odd r b=0 := by
  rw [boundaryTerm,upperCutoff_odd_small hr,intervalIntegral.integral_same]

theorem boundaryTerm_depth_zero (n : ℕ) (i : Side) {r b : ℝ} (hr : r ≤ (n:ℝ)+1) :
    boundaryTerm (n+2) i r b=0 := by
  induction n generalizing i r b with
  | zero =>
    cases i with
    | odd => exact boundaryTerm_odd_small 1 (by norm_num at hr; linarith)
    | even =>
      rw [boundaryTerm]
      calc
        _ = ∫ _x in (1:ℝ)..upperCutoff .even r b,(0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le (upperCutoff_bounds .even r b).1] at hx
          dsimp only [Side.flip]
          rw [boundaryTerm_odd_small 0 (by norm_num at hr; linarith [hx.1]),zero_div]
        _ = 0 := by simp
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,boundaryTerm]
    calc
      _ = ∫ _x in (1:ℝ)..upperCutoff i r b,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
        dsimp only
        have hchild : r-x ≤ (n:ℝ)+1 := by push_cast at hr; linarith [hx.1]
        rw [ih i.flip hchild,zero_div]
      _ = 0 := by simp

end ErdosContinuousBoundary

end

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

noncomputable def boundaryIntegrand (n : ℕ) (i : Side) (r x : ℝ) : ℝ :=
  boundaryTerm n i.flip (r-x) x/(max 1 x)

theorem boundaryIntegrand_continuous (n : ℕ) (i : Side) (r : ℝ) :
    Continuous (boundaryIntegrand n i r) := by
  have hc : Continuous (fun x : ℝ => boundaryTerm n i.flip (r-x) x) :=
    (boundaryTerm_continuous n i.flip).comp ((continuous_const.sub continuous_id).prodMk continuous_id)
  have hd : Continuous (fun x : ℝ => (max 1 x)⁻¹) :=
    (continuous_const.max continuous_id).inv₀ (fun x => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left 1 x)))
  have he : boundaryIntegrand n i r = (fun x => boundaryTerm n i.flip (r-x) x)*(fun x => (max 1 x)⁻¹) := by
    funext x
    exact div_eq_mul_inv _ _
  rw [he]
  exact hc.mul hd

theorem boundaryIntegrand_integrable (n : ℕ) (i : Side) (r a b : ℝ) :
    IntervalIntegrable (boundaryIntegrand n i r) volume a b :=
  (boundaryIntegrand_continuous n i r).intervalIntegrable a b

theorem boundaryTerm_nonnegative (n : ℕ) (i : Side) (r b : ℝ) : 0 ≤ boundaryTerm n i r b := by
  induction n generalizing i r b with
  | zero => exact zero_le_one
  | succ n ih =>
    apply intervalIntegral.integral_nonneg_of_forall (upperCutoff_bounds i r b).1
    intro x
    exact div_nonneg (ih i.flip (r-x) x) (le_trans zero_le_one (le_max_left 1 x))

theorem boundaryTerm_abs_le_one (n : ℕ) (i : Side) (r b : ℝ) : |boundaryTerm n i r b| ≤ 1 := by
  induction n generalizing i r b with
  | zero => norm_num [boundaryTerm]
  | succ n ih =>
    have hf (x : ℝ) : |boundaryTerm n i.flip (r-x) x/(max 1 x)| ≤ 1 := by
      have hd : 0 < max (1:ℝ) x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      rw [abs_div,abs_of_pos hd]
      exact (div_le_one hd).mpr ((ih i.flip (r-x) x).trans (le_max_left 1 x))
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=1) (b:=upperCutoff i r b)
      (C:=1) (f:=fun x => boundaryTerm n i.flip (r-x) x/(max 1 x))
      (fun x _ => by simpa only [Real.norm_eq_abs] using hf x)
    have hc := upperCutoff_bounds i r b
    change |boundaryTerm (n+1) i r b| ≤ 1
    rw [Real.norm_eq_abs,one_mul,abs_of_nonneg (by linarith : 0 ≤ upperCutoff i r b-1)] at h
    exact h.trans (by linarith)

theorem boundaryIntegrand_abs_le_one (n : ℕ) (i : Side) (r x : ℝ) :
    |boundaryIntegrand n i r x| ≤ 1 := by
  have hd : 0 < max (1:ℝ) x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  rw [boundaryIntegrand,abs_div,abs_of_pos hd]
  exact (div_le_one hd).mpr ((boundaryTerm_abs_le_one n i.flip (r-x) x).trans (le_max_left 1 x))

end ErdosContinuousBoundary

end

section

namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem boundaryTerm_r_difference (n : ℕ) (i : Side) (b r s : ℝ) :
    |boundaryTerm n i r b-boundaryTerm n i s b| ≤ (n:ℝ)*|r-s| := by
  induction n generalizing i b r s with
  | zero => simp [boundaryTerm]
  | succ n ih =>
    let D : ℝ := (n:ℝ)*|r-s|
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hFG (x : ℝ) : |boundaryIntegrand n i r x-boundaryIntegrand n i s x| ≤ D := by
      have hd : 0 < max (1:ℝ) x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have hnum := ih i.flip x (r-x) (s-x)
      have he : (r-x)-(s-x)=r-s := by ring
      rw [he] at hnum
      unfold boundaryIntegrand
      rw [← sub_div,abs_div,abs_of_pos hd]
      exact (div_le_div_of_nonneg_right hnum hd.le).trans (div_le_self hD (le_max_left 1 x))
    have h := integral_upper_difference_bound
      (boundaryIntegrand n i r) (boundaryIntegrand n i s)
      (boundaryIntegrand_continuous n i r) (boundaryIntegrand_continuous n i s)
      (upperCutoff i r b) (upperCutoff i s b) D (upperCutoff_bounds i r b) hD hFG
      (boundaryIntegrand_abs_le_one n i s)
    have hc := upperCutoff_r_difference i b r s
    have hh : |boundaryTerm (n+1) i r b-boundaryTerm (n+1) i s b| ≤ D+|r-s| :=
      h.trans (add_le_add le_rfl hc)
    simpa only [D,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hh

theorem boundaryTerm_b_difference (n : ℕ) (i : Side) (r b c : ℝ) :
    |boundaryTerm n i r b-boundaryTerm n i r c| ≤ |b-c| := by
  cases n with
  | zero => simp [boundaryTerm]
  | succ n =>
    have h := integral_upper_difference_bound
      (boundaryIntegrand n i r) (boundaryIntegrand n i r)
      (boundaryIntegrand_continuous n i r) (boundaryIntegrand_continuous n i r)
      (upperCutoff i r b) (upperCutoff i r c) 0 (upperCutoff_bounds i r b) le_rfl
      (by intro x; simp) (boundaryIntegrand_abs_le_one n i r)
    have hh : |boundaryTerm (n+1) i r b-boundaryTerm (n+1) i r c| ≤
        |upperCutoff i r b-upperCutoff i r c| := by simpa only [zero_add] using! h
    exact hh.trans (upperCutoff_b_difference i r b c)

theorem boundaryTerm_child_lipschitz (n : ℕ) (i : Side) (r : ℝ) :
    LipschitzWith ((n:NNReal)+1) (fun x => boundaryTerm n i (r-x) x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  have h1 := boundaryTerm_r_difference n i x (r-x) (r-y)
  have he : (r-x)-(r-y)=-(x-y) := by ring
  rw [he,abs_neg] at h1
  have h2 := boundaryTerm_b_difference n i (r-y) x y
  calc
    _ = |(boundaryTerm n i (r-x) x-boundaryTerm n i (r-y) x)+
        (boundaryTerm n i (r-y) x-boundaryTerm n i (r-y) y)| := by congr 1; ring
    _ ≤ |boundaryTerm n i (r-x) x-boundaryTerm n i (r-y) x|+
        |boundaryTerm n i (r-y) x-boundaryTerm n i (r-y) y| := abs_add_le _ _
    _ ≤ (n:ℝ)*|x-y|+|x-y| := add_le_add h1 h2
    _ = _ := by ring

end ErdosContinuousBoundary

end

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission
open NumberTheoryLean.HarmonicPrimeAtomicMeasure NumberTheoryLean.HarmonicReferenceMeasure
open ErdosMonotoneQuadrature

def boundaryGateSet (i : Side) (r b : ℝ) (closed : Bool) : Set ℝ :=
  {x | 1 < x ∧ x ≤ 2 ∧ (if closed then x ≤ b else x < b) ∧ childAdmitted i r x}

theorem boundaryGateSet_closed (i : Side) (r b : ℝ) :
    boundaryGateSet i r b true=Ioc 1 (upperCutoff i r b) := by
  ext x
  exact (mem_upperCutoff i r b x).symm

theorem boundaryGateSet_open_inter (i : Side) (r b : ℝ) :
    boundaryGateSet i r b false=Ioc 1 (upperCutoff i r b) ∩ Iio b := by
  rw [← boundaryGateSet_closed]
  ext x
  change (1 < x ∧ x ≤ 2 ∧ x < b ∧ childAdmitted i r x) ↔
    (1 < x ∧ x ≤ 2 ∧ x ≤ b ∧ childAdmitted i r x) ∧ x < b
  constructor
  · rintro ⟨h1,h2,hb,hg⟩
    exact ⟨⟨h1,h2,hb.le,hg⟩,hb⟩
  · rintro ⟨⟨h1,h2,_hb,hg⟩,hb⟩
    exact ⟨h1,h2,hb,hg⟩

theorem boundaryGateSet_open_diff (i : Side) (r b : ℝ) :
    boundaryGateSet i r b false=Ioc 1 (upperCutoff i r b) \ {b} := by
  rw [← boundaryGateSet_closed]
  ext x
  change (1 < x ∧ x ≤ 2 ∧ x < b ∧ childAdmitted i r x) ↔
    (1 < x ∧ x ≤ 2 ∧ x ≤ b ∧ childAdmitted i r x) ∧ x ≠ b
  constructor
  · rintro ⟨h1,h2,hb,hg⟩
    exact ⟨⟨h1,h2,hb.le,hg⟩,ne_of_lt hb⟩
  · rintro ⟨⟨h1,h2,hb,hg⟩,hne⟩
    exact ⟨h1,h2,lt_of_le_of_ne hb hne,hg⟩

theorem boundaryGateSet_orderConnected (i : Side) (r b : ℝ) (closed : Bool) :
    (boundaryGateSet i r b closed).OrdConnected := by
  cases closed with
  | false => rw [boundaryGateSet_open_inter]; exact ordConnected_Ioc.inter ordConnected_Iio
  | true => rw [boundaryGateSet_closed]; exact ordConnected_Ioc

theorem boundaryGateSet_subset (i : Side) (r b : ℝ) (closed : Bool) :
    boundaryGateSet i r b closed ⊆ Icc 1 2 := fun _ hx => ⟨hx.1.le,hx.2.1⟩

theorem boundary_reference_integral (g : ℝ → ℝ) {J : Set ℝ}
    (hJ : MeasurableSet J) (hsub : J ⊆ Icc 1 2) :
    (∫ x in J,g x ∂referenceMeasure 1 2)=∫ x in J,g x/x := by
  rw [referenceMeasure,reciprocalMeasure_integral _ (by norm_num : (0:ℝ)<1) _ hJ,
    Measure.restrict_restrict hJ,inter_eq_left.mpr hsub]
  apply setIntegral_congr_fun hJ
  intro x hx
  dsimp only
  rw [reciprocalWeight_eq (hsub hx).1]
  simp only [div_eq_mul_inv,mul_comm]

theorem boundaryTerm_gate_integral (n : ℕ) (i : Side) (r b : ℝ) (closed : Bool) :
    (∫ x in boundaryGateSet i r b closed,boundaryTerm n i.flip (r-x) x ∂referenceMeasure 1 2)=
      boundaryTerm (n+1) i r b := by
  rw [boundary_reference_integral _ (boundaryGateSet_orderConnected i r b closed).measurableSet
    (boundaryGateSet_subset i r b closed),boundaryTerm_reciprocal,
    intervalIntegral.integral_of_le (upperCutoff_bounds i r b).1]
  cases closed with
  | true => rw [boundaryGateSet_closed]
  | false =>
    rw [boundaryGateSet_open_diff]
    exact setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton b))

end ErdosContinuousBoundary

end

end Erdos970

end OAI
