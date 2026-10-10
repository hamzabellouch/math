import Mathlib
import OAI.Probability.JammingConcavity.FamilyPathRatio

namespace OAI

/-! Row Bounded Terminal. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open scoped BigOperators Classical
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder
open scoped BigOperators RealInnerProductSpace
open scoped NNReal Topology BigOperators
open scoped NNReal BigOperators RealInnerProductSpace
open scoped ENNReal NNReal BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace MicroscopicJamming

structure RowBoundedTerminal (u : ℝ → ℝ) (L H : ℝ) : Prop where
  diff : Differentiable ℝ u
  diff_deriv : Differentiable ℝ (deriv u)
  L_nonneg : 0 ≤ L
  H_nonneg : 0 ≤ H
  slope : ∀ x, |deriv u x| ≤ L
  curvature : ∀ x, |deriv (deriv u) x| ≤ H

def rowBoundedExpFirst (a : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  a*deriv u x*Real.exp (a*u x)
def rowBoundedExpSecond (a : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (a*deriv (deriv u) x+a^2*(deriv u x)^2)*Real.exp (a*u x)

lemma rowBounded_exp_derivatives {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) (a : ℝ) :
    (∀ x, HasDerivAt (fun y => Real.exp (a*u y)) (rowBoundedExpFirst a u x) x) ∧
    (∀ x, HasDerivAt (rowBoundedExpFirst a u) (rowBoundedExpSecond a u x) x) := by
  constructor
  · intro x
    convert ((hu.diff x).hasDerivAt.const_mul a).exp using 1; first | rfl | (simp only [rowBoundedExpFirst]; ring)
  · intro x
    convert (((hu.diff_deriv x).hasDerivAt.const_mul a).mul (((hu.diff x).hasDerivAt.const_mul a).exp)) using 1 <;> first | rfl | (simp only [rowBoundedExpSecond]; ring)

lemma rowBounded_exp_measurable {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) (a : ℝ) :
    Measurable (fun y => Real.exp (a*u y)) ∧ Measurable (rowBoundedExpFirst a u) ∧
      Measurable (rowBoundedExpSecond a u) := by
  refine ⟨(hu.diff.continuous.measurable.const_mul a).exp,?_,?_⟩
  · exact ((measurable_deriv u).const_mul a).mul (hu.diff.continuous.measurable.const_mul a).exp
  · exact (((measurable_deriv (deriv u)).const_mul a).add
      (((measurable_deriv u).pow_const 2).const_mul (a^2))).mul
        (hu.diff.continuous.measurable.const_mul a).exp

lemma rowBounded_exp_growth {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) (a : ℝ) :
    RowExpGrowth (fun y => Real.exp (a*u y)) ∧ RowExpGrowth (rowBoundedExpFirst a u) ∧
      RowExpGrowth (rowBoundedExpSecond a u) := by
  have he := RowExpGrowth.exp_bounded_deriv hu.diff hu.L_nonneg hu.slope a
  refine ⟨he,?_,?_⟩
  · apply he.mul_bounded (mul_nonneg (abs_nonneg a) hu.L_nonneg)
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hu.slope x) (abs_nonneg a)
  · apply he.mul_bounded (add_nonneg (mul_nonneg (abs_nonneg a) hu.H_nonneg) (mul_nonneg (sq_nonneg a) (sq_nonneg L)))
    intro x
    calc
      _ ≤ |a*deriv (deriv u) x|+|a^2*(deriv u x)^2| := abs_add_le _ _
      _ ≤ |a| * H+a^2*L^2 := by
        rw [abs_mul,abs_of_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg _))]
        apply add_le_add (mul_le_mul_of_nonneg_left (hu.curvature x) (abs_nonneg a))
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
        nlinarith [hu.slope x,sq_abs (deriv u x),abs_nonneg (deriv u x),hu.L_nonneg]

lemma rowBounded_tilt_slope {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) (a T x : ℝ) :
    |rowTiltStep a T u x (deriv u)| ≤ L :=
  rowTiltStep_abs_bound hu.diff.continuous.measurable (rowBounded_exp_growth hu a).1
    (measurable_deriv u) hu.L_nonneg hu.slope T x

lemma rowBounded_tilt_curvature {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) (a T x : ℝ) :
    |rowTiltStep a T u x (deriv (deriv u))| ≤ H :=
  rowTiltStep_abs_bound hu.diff.continuous.measurable (rowBounded_exp_growth hu a).1
    (measurable_deriv (deriv u)) hu.H_nonneg hu.curvature T x

lemma rowBounded_tilt_slope_square {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) (a T x : ℝ) :
    |rowTiltStep a T u x (fun y => (deriv u y)^2)| ≤ L^2 := by
  apply rowTiltStep_abs_bound hu.diff.continuous.measurable (rowBounded_exp_growth hu a).1
    ((measurable_deriv u).pow_const 2) (sq_nonneg L) _ T x
  intro y
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [hu.slope y,sq_abs (deriv u y),abs_nonneg (deriv u y),hu.L_nonneg]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace MicroscopicJamming

lemma rowBoundedOperator_derivatives {u : ℝ → ℝ} {L H : ℝ}
    (hu : RowBoundedTerminal u L H) (a T : ℝ) :
    (∀ x, HasDerivAt (gaussianRowOperator a T u) (rowTiltStep a T u x (deriv u)) x) ∧
    (∀ x, HasDerivAt (deriv (gaussianRowOperator a T u))
      (rowTiltStep a T u x (deriv (deriv u))+
        a*(rowTiltStep a T u x (fun y => (deriv u y)^2)-(rowTiltStep a T u x (deriv u))^2)) x) := by
  by_cases haz : a=0
  · subst a
    have hd := rowExpHeat_space_derivative hu.diff.continuous.measurable (measurable_deriv u)
      (RowExpGrowth.of_bounded_deriv hu.diff hu.L_nonneg hu.slope)
      (RowExpGrowth.bounded hu.L_nonneg hu.slope) (fun y => (hu.diff y).hasDerivAt) T
    have hd' := rowExpHeat_space_derivative (measurable_deriv u) (measurable_deriv (deriv u))
      (RowExpGrowth.bounded hu.L_nonneg hu.slope) (RowExpGrowth.bounded hu.H_nonneg hu.curvature)
      (fun y => (hu.diff_deriv y).hasDerivAt) T
    have he : gaussianRowOperator 0 T u=gaussianHeat u T := by funext x; simp [gaussianRowOperator]
    have hde : deriv (gaussianRowOperator 0 T u)=gaussianHeat (deriv u) T := by
      rw [he]; exact funext (fun x => (hd x).deriv)
    constructor
    · intro x
      rw [he]
      simpa only [rowTiltStep,zero_mul,Real.exp_zero,mul_one,integral_const,
        probReal_univ,smul_eq_mul,one_mul,div_one,gaussianHeat] using hd x
    · intro x
      rw [hde]
      simpa only [rowTiltStep,zero_mul,Real.exp_zero,mul_one,integral_const,
        probReal_univ,smul_eq_mul,one_mul,div_one,gaussianHeat,add_zero] using hd' x
  · obtain ⟨hm,hm₁,hm₂⟩ := rowBounded_exp_measurable hu a
    obtain ⟨hg,hg₁,hg₂⟩ := rowBounded_exp_growth hu a
    obtain ⟨hd,hd₁⟩ := rowBounded_exp_derivatives hu a
    have hp (y : ℝ) : gaussianHeat (fun z => Real.exp (a*u z)) T y ≠ 0 :=
      (integral_exp_pos (hg.integrable_affine hm y (Real.sqrt T))).ne'
    have hx := rowExpHeat_space_derivative hm hm₁ hg hg₁ hd T
    have hxx := rowExpHeat_space_derivative hm₁ hm₂ hg₁ hg₂ hd₁ T
    have he : gaussianRowOperator a T u =
        fun y => (1/a)*Real.log (gaussianHeat (fun z => Real.exp (a*u z)) T y) := by
      funext y; simp only [gaussianRowOperator,ite_eq_right haz]
    have hdg (y : ℝ) : HasDerivAt (gaussianRowOperator a T u)
        ((1/a)*(gaussianHeat (rowBoundedExpFirst a u) T y/gaussianHeat (fun z => Real.exp (a*u z)) T y)) y := by
      rw [he]; exact ((hx y).log (hp y)).const_mul _
    have hdge : deriv (gaussianRowOperator a T u) =
        fun y => (1/a)*(gaussianHeat (rowBoundedExpFirst a u) T y/gaussianHeat (fun z => Real.exp (a*u z)) T y) :=
      funext fun y => (hdg y).deriv
    have hfirst (x : ℝ) : gaussianHeat (rowBoundedExpFirst a u) T x =
        a*(∫ z,deriv u (x+Real.sqrt T*z)*Real.exp (a*u (x+Real.sqrt T*z)) ∂gaussianReal 0 1) := by
      rw [← integral_const_mul]
      unfold gaussianHeat rowBoundedExpFirst
      congr 1; funext z; ring
    have hsecond (x : ℝ) : gaussianHeat (rowBoundedExpSecond a u) T x =
        a*(∫ z,deriv (deriv u) (x+Real.sqrt T*z)*Real.exp (a*u (x+Real.sqrt T*z)) ∂gaussianReal 0 1)+
        a^2*(∫ z,(deriv u (x+Real.sqrt T*z))^2*Real.exp (a*u (x+Real.sqrt T*z)) ∂gaussianReal 0 1) := by
      have hi := rowTiltStep_product_integrable hu.diff.continuous.measurable hg
        (measurable_deriv (deriv u)) hu.H_nonneg hu.curvature T x
      have hi' := rowTiltStep_product_integrable hu.diff.continuous.measurable hg
        ((measurable_deriv u).pow_const 2) (sq_nonneg L) (fun y => show |(deriv u y)^2| ≤ L^2 by
          rw [abs_of_nonneg (sq_nonneg _)]
          nlinarith [hu.slope y,sq_abs (deriv u y),abs_nonneg (deriv u y),hu.L_nonneg]) T x
      rw [← integral_const_mul,← integral_const_mul,← integral_add (hi.const_mul a) (hi'.const_mul (a^2))]
      unfold gaussianHeat rowBoundedExpSecond
      congr 1; funext z; ring
    constructor
    · intro x
      convert hdg x using 1
      rw [hfirst]
      unfold rowTiltStep gaussianHeat
      field_simp [haz]
    · intro x
      have hdd : HasDerivAt (deriv (gaussianRowOperator a T u))
          ((1/a)*((gaussianHeat (rowBoundedExpSecond a u) T x*gaussianHeat (fun z => Real.exp (a*u z)) T x-
            (gaussianHeat (rowBoundedExpFirst a u) T x)^2)/(gaussianHeat (fun z => Real.exp (a*u z)) T x)^2)) x := by
        rw [hdge]
        convert (((hxx x).div (hx x) (hp x)).const_mul (1/a)) using 1; first | rfl | simp only [pow_two]
      convert hdd using 1
      rw [hfirst,hsecond]
      have hn := hp x
      unfold rowTiltStep gaussianHeat at hn ⊢
      field_simp [haz,hn]
      ring

lemma rowBoundedOperator_terminal {u : ℝ → ℝ} {L H a : ℝ}
    (hu : RowBoundedTerminal u L H) (ha : 0 ≤ a) (ha1 : a ≤ 1) (T : ℝ) :
    RowBoundedTerminal (gaussianRowOperator a T u) L (H+2*L^2) := by
  have hd := rowBoundedOperator_derivatives hu a T
  refine ⟨fun x => (hd.1 x).differentiableAt,fun x => (hd.2 x).differentiableAt,
    hu.L_nonneg,add_nonneg hu.H_nonneg (mul_nonneg (by norm_num) (sq_nonneg L)),?_,?_⟩
  · intro x
    rw [(hd.1 x).deriv]
    exact rowBounded_tilt_slope hu a T x
  · intro x
    rw [(hd.2 x).deriv]
    have hJ := rowBounded_tilt_curvature hu a T x
    have hD := rowBounded_tilt_slope hu a T x
    have hV := rowBounded_tilt_slope_square hu a T x
    have hD2 : |(rowTiltStep a T u x (deriv u))^2| ≤ L^2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (rowTiltStep a T u x (deriv u)),abs_nonneg (rowTiltStep a T u x (deriv u)),hu.L_nonneg]
    calc
      _ ≤ |rowTiltStep a T u x (deriv (deriv u))|+
          |a*(rowTiltStep a T u x (fun y => (deriv u y)^2)-(rowTiltStep a T u x (deriv u))^2)| := abs_add_le _ _
      _ ≤ H + a*(|rowTiltStep a T u x (fun y => (deriv u y)^2)|+|(rowTiltStep a T u x (deriv u))^2|) := by
        rw [abs_mul,abs_of_nonneg ha]
        exact add_le_add hJ (mul_le_mul_of_nonneg_left (abs_sub _ _) ha)
      _ ≤ H + a*(2*L^2) := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith) ha)
      _ ≤ H + 2*L^2 := by nlinarith [sq_nonneg L]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace MicroscopicJamming

lemma rowBoundedComposition_terminal {u : ℝ → ℝ} {L H : ℝ}
    (hu : RowBoundedTerminal u L H) (rs : List (ℝ × ℝ))
    (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) :
    ∃ K, RowBoundedTerminal (gaussianRowComposition rs u) L K := by
  induction rs with
  | nil => exact ⟨H,hu⟩
  | cons r rs ih =>
    rcases r with ⟨a,T⟩
    obtain ⟨K,hK⟩ := ih (fun z hz => hrs z (List.mem_cons_of_mem (a,T) hz))
    have hr := hrs (a,T) (List.mem_cons_self)
    exact ⟨K+2*L^2,rowBoundedOperator_terminal hK hr.1 hr.2.1 T⟩

lemma rowDerivativeDepthMoment_nil (u : ℝ → ℝ) (i : ℕ) (x : ℝ) :
    rowDerivativeDepthMoment [] u i x=(deriv u x)^2 := by
  cases i <;> rfl

lemma measurable_rowDerivativeDepthMoment {u : ℝ → ℝ} {L H : ℝ}
    (hu : RowBoundedTerminal u L H) (rs : List (ℝ × ℝ))
    (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) (i : ℕ) :
    Measurable (rowDerivativeDepthMoment rs u i) := by
  induction rs generalizing i with
  | nil => simpa only [funext (rowDerivativeDepthMoment_nil u i)] using (measurable_deriv u).pow_const 2
  | cons r rs ih =>
    rcases r with ⟨a,T⟩
    have ht := fun z hz => hrs z (List.mem_cons_of_mem (a,T) hz)
    obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hu rs ht
    cases i with
    | zero => exact (measurable_deriv _).pow_const 2
    | succ i => exact measurable_rowTiltStep hK.diff.continuous.measurable (ih ht i) a T

lemma rowDerivativeDepthMoment_bounds {u : ℝ → ℝ} {L H : ℝ}
    (hu : RowBoundedTerminal u L H) (rs : List (ℝ × ℝ))
    (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) (i : ℕ) (x : ℝ) :
    0 ≤ rowDerivativeDepthMoment rs u i x ∧ rowDerivativeDepthMoment rs u i x ≤ L^2 := by
  induction rs generalizing i x with
  | nil =>
    rw [rowDerivativeDepthMoment_nil]
    refine ⟨sq_nonneg _,?_⟩
    nlinarith [hu.slope x,sq_abs (deriv u x),abs_nonneg (deriv u x),hu.L_nonneg]
  | cons r rs ih =>
    rcases r with ⟨a,T⟩
    have ht := fun z hz => hrs z (List.mem_cons_of_mem (a,T) hz)
    cases i with
    | zero =>
      obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hu ((a,T)::rs) hrs
      change 0 ≤ (deriv (gaussianRowComposition ((a,T)::rs) u) x)^2 ∧ (deriv (gaussianRowComposition ((a,T)::rs) u) x)^2 ≤ L^2
      refine ⟨sq_nonneg _,?_⟩
      nlinarith [hK.slope x,sq_abs (deriv (gaussianRowComposition ((a,T)::rs) u) x),
        abs_nonneg (deriv (gaussianRowComposition ((a,T)::rs) u) x),hu.L_nonneg]
    | succ i =>
      obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hu rs ht
      change 0 ≤ rowTiltStep a T _ x _ ∧ rowTiltStep a T _ x _ ≤ L^2
      refine ⟨rowTiltStep_nonneg (fun y => (ih ht i y).1),?_⟩
      have hb : ∀ y, |rowDerivativeDepthMoment rs u i y| ≤ L^2 := by
        intro y; rw [abs_of_nonneg (ih ht i y).1]; exact (ih ht i y).2
      exact le_trans (le_abs_self _) (rowTiltStep_abs_bound hK.diff.continuous.measurable
        (rowBounded_exp_growth hK a).1 (measurable_rowDerivativeDepthMoment hu rs ht i)
        (sq_nonneg L) hb T x)

lemma rowDerivativeDepthMoment_monotone {u : ℝ → ℝ} {L H : ℝ}
    (hu : RowBoundedTerminal u L H) (rs : List (ℝ × ℝ))
    (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) (x : ℝ) :
    Monotone (fun i => rowDerivativeDepthMoment rs u i x) := by
  induction rs generalizing x with
  | nil => intro i j hij; simp only [rowDerivativeDepthMoment_nil]; rfl
  | cons r rs ih =>
    rcases r with ⟨a,T⟩
    have ht := fun z hz => hrs z (List.mem_cons_of_mem (a,T) hz)
    obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hu rs ht
    apply monotone_nat_of_le_succ
    intro i
    cases i with
    | zero =>
      simp only [rowDerivativeDepthMoment,gaussianRowComposition]
      rw [show rowDerivativeDepthMoment rs u 0 = (fun y => (deriv (gaussianRowComposition rs u) y)^2) from
        funext (fun y => rowDerivativeDepthMoment.eq_1 rs u y)]
      rw [((rowBoundedOperator_derivatives hK a T).1 x).deriv]
      exact rowTiltStep_square_ge hK.diff.continuous.measurable (rowBounded_exp_growth hK a).1
        (measurable_deriv _) hu.L_nonneg hK.slope T x
    | succ i =>
      change rowTiltStep a T _ x (rowDerivativeDepthMoment rs u i) ≤
        rowTiltStep a T _ x (rowDerivativeDepthMoment rs u (i+1))
      have hb (j y) : |rowDerivativeDepthMoment rs u j y| ≤ L^2 := by
        have hy := rowDerivativeDepthMoment_bounds hu rs ht j y
        rw [abs_of_nonneg hy.1]; exact hy.2
      exact rowTiltStep_mono hK.diff.continuous.measurable (rowBounded_exp_growth hK a).1
        (measurable_rowDerivativeDepthMoment hu rs ht i)
        (measurable_rowDerivativeDepthMoment hu rs ht (i+1))
        (sq_nonneg L) (sq_nonneg L) (hb i) (hb (i+1))
        (fun y => ih ht y (Nat.le_succ i)) T x
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace MicroscopicJamming

lemma rowDerivativeDepthMoment_plateau {u : ℝ → ℝ} {L H : ℝ}
    (hu : RowBoundedTerminal u L H) (rs : List (ℝ × ℝ))
    (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) :
    ∀ i : Fin rs.length, (rs.get i).2=0 → ∀ x,
      rowDerivativeDepthMoment rs u i.val x=rowDerivativeDepthMoment rs u (i.val+1) x := by
  induction rs with
  | nil => intro i; exact Fin.elim0 i
  | cons r rs ih =>
    rcases r with ⟨a,T⟩
    have ht := fun z hz => hrs z (List.mem_cons_of_mem (a,T) hz)
    obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hu rs ht
    intro i
    refine Fin.cases ?_ ?_ i
    · intro hz x
      change T=0 at hz
      simp only [Fin.val_zero,rowDerivativeDepthMoment,gaussianRowComposition]
      rw [show rowDerivativeDepthMoment rs u 0 = (fun y => (deriv (gaussianRowComposition rs u) y)^2) from
        funext (fun y => rowDerivativeDepthMoment.eq_1 rs u y)]
      rw [((rowBoundedOperator_derivatives hK a T).1 x).deriv,hz]
      rw [rowTiltStep_zero,rowTiltStep_zero]
    · intro j hz x
      change (rs.get j).2=0 at hz
      change rowTiltStep a T (gaussianRowComposition rs u) x (rowDerivativeDepthMoment rs u j.val) =
        rowTiltStep a T (gaussianRowComposition rs u) x (rowDerivativeDepthMoment rs u (j.val+1))
      rw [funext (ih ht j hz)]

theorem gaussianDerivativeMartingale : GaussianDerivativeMartingaleStatement := by
  intro u L H hu hL hH hb rs hrs
  have hu' : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have ht : RowBoundedTerminal u L H :=
    ⟨hu.differentiable (by norm_num),hu'.differentiable (by norm_num),hL,hH,
      fun x => (hb x).1,fun x => (hb x).2⟩
  obtain ⟨K,hK⟩ := rowBoundedComposition_terminal ht rs hrs
  refine ⟨⟨hK.diff,hK.diff_deriv⟩,?_,rowDerivativeDepthMoment_bounds ht rs hrs,
    rowDerivativeDepthMoment_monotone ht rs hrs,rowDerivativeDepthMoment_plateau ht rs hrs⟩
  intro a T ha ha1 hT x
  exact ((rowBoundedOperator_derivatives hK a T).1 x).deriv
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace MicroscopicJamming

lemma rowGaussianLaw_map (d : ℝ≥0) :
    (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt d*z) = gaussianReal 0 d := by
  convert gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt d) using 1
  · simp

lemma rowGaussian_integral (d : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ a, f a ∂gaussianReal 0 d) = ∫ z, f (Real.sqrt d*z) ∂gaussianReal 0 1 := by
  rw [← rowGaussianLaw_map d]
  exact integral_map (by fun_prop) hf.aestronglyMeasurable

lemma rowGaussian_lintegral (d : ℝ≥0) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a, f a ∂gaussianReal 0 d) = ∫⁻ z, f (Real.sqrt d*z) ∂gaussianReal 0 1 := by
  rw [← rowGaussianLaw_map d]
  exact lintegral_map hf (by fun_prop)

lemma rowGaussian_integrable (d : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f (gaussianReal 0 d) ↔
      Integrable (fun z => f (Real.sqrt d*z)) (gaussianReal 0 1) := by
  rw [← rowGaussianLaw_map d]
  exact integrable_map_measure hf.aestronglyMeasurable (by fun_prop)

lemma rowGaussianBlocks_valid (ms : List ℝ) (hms : ∀ m ∈ ms, 0 ≤ m ∧ m ≤ 1)
    (d : ℕ → ℝ≥0) : ∀ r ∈ rowGaussianBlocks ms d, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2 := by
  induction ms generalizing d with
  | nil => simp [rowGaussianBlocks]
  | cons m ms ih =>
    intro r hr
    rcases List.mem_cons.mp hr with hr|hr
    · subst r; exact ⟨(hms m (by simp)).1,(hms m (by simp)).2,(d 0).coe_nonneg⟩
    · exact ih (fun a ha => hms a (by simp [ha])) _ r hr

lemma rowGaussian_recursion {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (ms : List ℝ) (hms : ∀ m ∈ ms, 0 < m ∧ m < 1) (d : ℕ → ℝ≥0) :
    (familyRecursion ms (rowGaussianLaw d) u = gaussianRowComposition (rowGaussianBlocks ms d) u) ∧
    FamilyMomentsFinite ms (rowGaussianLaw d) u := by
  induction ms generalizing d with
  | nil => exact ⟨rfl, trivial⟩
  | cons m ms ih =>
    have hm := hms m (by simp)
    have ht : ∀ a ∈ ms, 0 < a ∧ a < 1 := fun a ha => hms a (by simp [ha])
    obtain ⟨he,hi⟩ := ih ht (fun j => d (j+1))
    obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hu (rowGaussianBlocks ms (fun j => d (j+1)))
      (rowGaussianBlocks_valid ms (fun a ha => ⟨(ht a ha).1.le,(ht a ha).2.le⟩) _)
    have hm' : m ≠ 0 := ne_of_gt hm.1
    have hν : (fun j => rowGaussianLaw d (j+1)) = rowGaussianLaw (fun j => d (j+1)) := rfl
    have hmF (x : ℝ) : Measurable (fun a => Real.exp (m*gaussianRowComposition
        (rowGaussianBlocks ms (fun j => d (j+1))) u (x+a))) := by
      exact ((hK.diff.continuous.measurable.comp (by fun_prop)).const_mul m).exp
    constructor
    · funext x
      simp only [familyRecursion, hν, he, rowGaussianBlocks, gaussianRowComposition,
        gaussianRowOperator, ite_eq_right hm']
      exact congrArg (fun z => 1/m*Real.log z) (rowGaussian_integral (d 0) (hmF x))
    · refine ⟨?_,hi⟩
      intro x
      change Integrable (fun a => Real.exp (m*familyRecursion ms
        (rowGaussianLaw (fun j => d (j+1))) u (x+a))) (gaussianReal 0 (d 0))
      rw [he, rowGaussian_integrable (d 0) (hmF x)]
      exact rowTiltStep_weight_integrable hK.diff.continuous.measurable
        (rowBounded_exp_growth hK m).1 (d 0) x

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace MicroscopicJamming

instance rowSingleIndexUnique (φ : ℝ → ℝ≥0∞) : (k : ℕ) →
    Unique (MarkedPatternIndex k (rowSinglePattern φ k))
  | 0 => inferInstanceAs (Unique (Fin 1))
  | k+1 => by
    change Unique ((i : Fin 1) × MarkedPatternIndex k ([rowSinglePattern φ k].get i))
    letI (i : Fin 1) : Unique (MarkedPatternIndex k ([rowSinglePattern φ k].get i)) := by
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact rowSingleIndexUnique φ k
    exact (Equiv.sigmaUnique (Fin 1) _).unique

noncomputable def rowPairIndexEquiv (φ : ℝ → ℝ≥0∞) : (k j : ℕ) →
    MarkedPatternIndex k (rowPairPattern φ k j) ≃ Fin 2
  | 0, _ => Equiv.refl _
  | k+1, 0 => by
    change ((i : Fin 2) × MarkedPatternIndex k ([rowSinglePattern φ k,rowSinglePattern φ k].get i)) ≃ Fin 2
    letI (i : Fin 2) : Unique (MarkedPatternIndex k ([rowSinglePattern φ k,rowSinglePattern φ k].get i)) := by
      have hi : [rowSinglePattern φ k,rowSinglePattern φ k].get i = rowSinglePattern φ k := by
        fin_cases i <;> rfl
      rw [hi]
      exact rowSingleIndexUnique φ k
    exact Equiv.sigmaUnique _ _
  | k+1, j+1 => by
    change ((i : Fin 1) × MarkedPatternIndex k ([rowPairPattern φ k j].get i)) ≃ Fin 2
    have he (i : Fin 1) : MarkedPatternIndex k ([rowPairPattern φ k j].get i) ≃
        MarkedPatternIndex k (rowPairPattern φ k j) := by
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact Equiv.refl _
    exact ((Equiv.sigmaCongrRight he).trans (Equiv.sigmaEquivProd _ _)).trans
      ((Equiv.prodComm _ _).trans ((Equiv.prodUnique _ _).trans (rowPairIndexEquiv φ k j)))

lemma rowPairIndexEquiv_zero (φ : ℝ → ℝ≥0∞) (k : ℕ)
    (i : Fin 2) (b : MarkedPatternIndex k ([rowSinglePattern φ k,rowSinglePattern φ k].get i)) :
    rowPairIndexEquiv φ (k+1) 0 ⟨i,b⟩ = i := rfl

lemma rowPairIndexEquiv_succ (φ : ℝ → ℝ≥0∞) (k j : ℕ)
    (b : MarkedPatternIndex k (rowPairPattern φ k j)) :
    rowPairIndexEquiv φ (k+1) (j+1) (⟨(0 : Fin 1),b⟩ : (i : Fin 1) × MarkedPatternIndex k ([rowPairPattern φ k j].get i)) = rowPairIndexEquiv φ k j b := rfl

lemma familySampleObservable_single (φ : ℝ → ℝ≥0∞) (ms : List ℝ) (x : ℝ)
    (ω : FamilyCascadeTree ℝ ms.length) (p : CascadePath ms.length) :
    familySampleObservable ms (rowSinglePattern φ ms.length) x ω (fun _ => p) =
      φ (familyPathMark ms.length x ω p) := by
  induction ms generalizing x with
  | nil => rfl
  | cons m ms ih =>
    let a0 : {a : Fin 1 → CloudLabel // Function.Injective a} :=
      ⟨fun _ => p.1,fun i j _ => Subsingleton.elim _ _⟩
    change (∑' a : {a : Fin 1 → CloudLabel // Function.Injective a},
      ∏ i : Fin 1, if ∀ j : MarkedPatternIndex ms.length ([rowSinglePattern φ ms.length].get i),
        p.1 = a.val i then
          familySampleObservable ms ([rowSinglePattern φ ms.length].get i)
            (x+(cloudLabelPoint ω (a.val i)).2.1) (cloudLabelPoint ω (a.val i)).2.2 (fun _ => p.2)
        else 0) = _
    simp only [Fin.prod_univ_one,List.get_cons_zero]
    rw [tsum_eq_single a0]
    · simp only [a0,forall_const,ite_true]
      exact ih _ _ _
    · intro a ha
      have hne : p.1 ≠ a.val 0 := by
        intro he
        apply ha
        apply Subtype.ext
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        simpa [a0,hi] using he.symm
      rw [ite_eq_right]
      intro hall
      exact hne (hall default)

lemma familySampleObservable_pair_zero (φ : ℝ → ℝ≥0∞) (m : ℝ) (ms : List ℝ) (x : ℝ)
    (ω : FamilyCascadeTree ℝ (m::ms).length) (ℓ : Fin 2 → CascadePath (m::ms).length) :
    familySampleObservable (m::ms) (rowPairPattern φ (m::ms).length 0) x ω
      (fun b => ℓ (rowPairIndexEquiv φ (m::ms).length 0 b)) =
    (if (ℓ 0).1 = (ℓ 1).1 then 0 else
      φ (familyPathMark (m::ms).length x ω (ℓ 0))*φ (familyPathMark (m::ms).length x ω (ℓ 1))) := by
  simp only [List.length_cons,rowPairPattern,familySampleObservable]
  change (∑' a : {a : Fin 2 → CloudLabel // Function.Injective a}, ∏ i : Fin 2, _) = _
  simp only [Fin.prod_univ_two]
  change (∑' a : {a : Fin 2 → CloudLabel // Function.Injective a},
    (if ∀ b : MarkedPatternIndex ms.length (rowSinglePattern φ ms.length), (ℓ 0).1 = a.val 0 then
      familySampleObservable ms (rowSinglePattern φ ms.length) (x+(cloudLabelPoint ω (a.val 0)).2.1)
        (cloudLabelPoint ω (a.val 0)).2.2 (fun _ => (ℓ 0).2) else 0) *
    (if ∀ b : MarkedPatternIndex ms.length (rowSinglePattern φ ms.length), (ℓ 1).1 = a.val 1 then
      familySampleObservable ms (rowSinglePattern φ ms.length) (x+(cloudLabelPoint ω (a.val 1)).2.1)
        (cloudLabelPoint ω (a.val 1)).2.2 (fun _ => (ℓ 1).2) else 0)) = _
  simp only [forall_const, familySampleObservable_single]
  by_cases hs : (ℓ 0).1 = (ℓ 1).1
  · rw [ite_eq_left hs]
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    by_cases h0 : (ℓ 0).1 = a.val 0
    · have h1 : (ℓ 1).1 ≠ a.val 1 := by
        intro h1
        have hh := a.property (h0.symm.trans (hs.trans h1))
        exact (by decide : (0:Fin 2) ≠ 1) hh
      rw [ite_eq_left h0,ite_eq_right h1,mul_zero]
    · rw [ite_eq_right h0,zero_mul]
  · rw [ite_eq_right hs]
    let a0 : {a : Fin 2 → CloudLabel // Function.Injective a} :=
      ⟨fun i => (ℓ i).1,by
        intro i j he
        fin_cases i <;> fin_cases j
        · rfl
        · exact (hs he).elim
        · exact (hs he.symm).elim
        · rfl⟩
    rw [tsum_eq_single a0]
    · simp only [a0]
      rfl
    · intro a ha
      by_cases h0 : (ℓ 0).1 = a.val 0
      · have h1 : (ℓ 1).1 ≠ a.val 1 := by
          intro h1
          apply ha
          apply Subtype.ext
          funext i
          fin_cases i
          · exact h0.symm
          · exact h1.symm
        rw [ite_eq_left h0,ite_eq_right h1,mul_zero]
      · rw [ite_eq_right h0,zero_mul]

lemma familySampleObservable_pair_succ (φ : ℝ → ℝ≥0∞) (m : ℝ) (ms : List ℝ) (j : ℕ) (x : ℝ)
    (ω : FamilyCascadeTree ℝ (m::ms).length) (ℓ : Fin 2 → CascadePath (m::ms).length) :
    familySampleObservable (m::ms) (rowPairPattern φ (m::ms).length (j+1)) x ω
      (fun b => ℓ (rowPairIndexEquiv φ (m::ms).length (j+1) b)) =
    (if (ℓ 0).1 = (ℓ 1).1 then
      familySampleObservable ms (rowPairPattern φ ms.length j) (x+(cloudLabelPoint ω (ℓ 0).1).2.1)
        (cloudLabelPoint ω (ℓ 0).1).2.2 (fun b => (ℓ (rowPairIndexEquiv φ ms.length j b)).2)
      else 0) := by
  simp only [List.length_cons,rowPairPattern,familySampleObservable]
  change (∑' a : {a : Fin 1 → CloudLabel // Function.Injective a}, ∏ i : Fin 1, _) = _
  simp only [Fin.prod_univ_one]
  change (∑' a : {a : Fin 1 → CloudLabel // Function.Injective a},
    if ∀ b : MarkedPatternIndex ms.length (rowPairPattern φ ms.length j),
        (ℓ (rowPairIndexEquiv φ ms.length j b)).1 = a.val 0 then
      familySampleObservable ms (rowPairPattern φ ms.length j) (x+(cloudLabelPoint ω (a.val 0)).2.1)
        (cloudLabelPoint ω (a.val 0)).2.2 (fun b => (ℓ (rowPairIndexEquiv φ ms.length j b)).2)
      else 0) = _
  have hall (a : CloudLabel) : (∀ b : MarkedPatternIndex ms.length (rowPairPattern φ ms.length j),
      (ℓ (rowPairIndexEquiv φ ms.length j b)).1 = a) ↔ (ℓ 0).1 = a ∧ (ℓ 1).1 = a := by
    constructor
    · intro hh
      exact ⟨by simpa using hh ((rowPairIndexEquiv φ ms.length j).symm 0),
        by simpa using hh ((rowPairIndexEquiv φ ms.length j).symm 1)⟩
    · rintro ⟨h0,h1⟩ b
      have hh : ∀ i : Fin 2, (ℓ i).1 = a := Fin.forall_fin_two.mpr ⟨h0,h1⟩
      exact hh _
  simp_rw [hall]
  by_cases hs : (ℓ 0).1 = (ℓ 1).1
  · rw [ite_eq_left hs]
    let a0 : {a : Fin 1 → CloudLabel // Function.Injective a} :=
      ⟨fun _ => (ℓ 0).1, fun i k _ => Subsingleton.elim _ _⟩
    rw [tsum_eq_single a0]
    · rw [ite_eq_left (show (ℓ 0).1 = a0.val 0 ∧ (ℓ 1).1 = a0.val 0 from ⟨rfl,hs.symm⟩)]
    · intro a ha
      apply ite_eq_right
      rintro ⟨h0,h1⟩
      apply ha
      apply Subtype.ext
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [a0,hi] using h0.symm
  · rw [ite_eq_right hs]
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    apply ite_eq_right
    rintro ⟨h0,h1⟩
    exact hs (h0.trans h1.symm)

lemma familySampleObservable_pair (φ : ℝ → ℝ≥0∞) (ms : List ℝ) (j : ℕ) (hj : j ≤ ms.length)
    (x : ℝ) (ω : FamilyCascadeTree ℝ ms.length) (ℓ : Fin 2 → CascadePath ms.length) :
    familySampleObservable ms (rowPairPattern φ ms.length j) x ω
      (fun b => ℓ (rowPairIndexEquiv φ ms.length j b)) = rowPairIidObservable ms φ j x ω ℓ := by
  induction ms generalizing x j with
  | nil =>
    have hj0 : j = 0 := by simpa using hj
    subst j
    change (φ x)^2 = φ x*φ x
    exact pow_two _
  | cons m ms ih =>
    cases j with
    | zero =>
      rw [familySampleObservable_pair_zero]
      by_cases hs : (ℓ 0).1 = (ℓ 1).1 <;>
        simp [rowPairIidObservable,cascadeSharedEdges,hs]
    | succ j =>
      rw [familySampleObservable_pair_succ]
      have hj' : j ≤ ms.length := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hj
      have he := ih j hj' (x+(cloudLabelPoint ω (ℓ 0).1).2.1)
        (cloudLabelPoint ω (ℓ 0).1).2.2 (fun i => (ℓ i).2)
      rw [he]
      by_cases hs : (ℓ 0).1 = (ℓ 1).1
      · simp only [ite_eq_left hs]
        simp only [rowPairIidObservable,List.length_cons,cascadeSharedEdges,ite_eq_left hs]
        have heq : (1+cascadeSharedEdges ms.length (ℓ 0).2 (ℓ 1).2 = j+1) ↔
            cascadeSharedEdges ms.length (ℓ 0).2 (ℓ 1).2 = j := by omega
        simp [heq,familyPathMark,cloudLabelPoint, ← hs]
      · simp [rowPairIidObservable,cascadeSharedEdges,hs]

theorem rowPairSemantic_proved : RowPairSemanticStatement := by
  intro ms φ j hj u x ω
  let := familySampleLeafLaw_probability ms u x ω
  let e := rowPairIndexEquiv φ ms.length j
  have hp := measurePreserving_piCongrLeft
    (fun _ : MarkedPatternIndex ms.length (rowPairPattern φ ms.length j) => familySampleLeafLaw ms u x ω) e.symm
  have he := hp.lintegral_comp (measurable_of_countable
    (familySampleObservable ms (rowPairPattern φ ms.length j) x ω))
  change _ = familySampleMean ms (rowPairPattern φ ms.length j) u x ω at he
  rw [← he]
  apply lintegral_congr
  intro ℓ
  have herr : (MeasurableEquiv.piCongrLeft (fun _ => CascadePath ms.length) e.symm) ℓ =
      (fun b => ℓ (rowPairIndexEquiv φ ms.length j b)) := by
    funext b
    simp only [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply,
      Equiv.symm_symm,eq_rec_constant,e]
  rw [herr]
  exact familySampleObservable_pair φ ms j hj x ω ℓ

end MicroscopicJamming

end

end OAI
