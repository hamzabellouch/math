import Mathlib
import OAI.Probability.JammingConcavity.RowZeroRefinementClosureRowDensityScoreIdentity

namespace OAI

/-! Row Finite Diagonal. -/

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
open scoped MatrixOrder
open scoped NNReal
open scoped BigOperators NNReal
open scoped NNReal ENNReal BigOperators Topology
open scoped Topology ENNReal NNReal
open scoped Matrix.Norms.L2Operator MatrixOrder Topology NNReal ENNReal BigOperators
open scoped Topology ENNReal NNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped Topology NNReal ENNReal BigOperators
open scoped BigOperators NNReal Topology
open scoped Topology NNReal ENNReal BigOperators MatrixOrder
open scoped Topology NNReal ENNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma RowExpGrowth.add {v w : ℝ → ℝ} (hv : RowExpGrowth v) (hw : RowExpGrowth w) :
    RowExpGrowth (fun x => v x+w x) := by
  obtain ⟨K,L,hK,hL,hv⟩ := hv
  obtain ⟨K',L',hK',hL',hw⟩ := hw
  refine ⟨K+K',L+L',by positivity,by positivity,fun x => ?_⟩
  calc
    _ ≤ |v x|+|w x| := abs_add_le _ _
    _ ≤ K*Real.exp (L*|x|)+K'*Real.exp (L'*|x|) := add_le_add (hv x) (hw x)
    _ ≤ K*Real.exp ((L+L')*|x|)+K'*Real.exp ((L+L')*|x|) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK
        nlinarith [abs_nonneg x]
      · apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK'
        nlinarith [abs_nonneg x]
    _ = _ := by ring

lemma rowExpGrowth_const (c : ℝ) : RowExpGrowth (fun _ : ℝ => c) :=
  RowExpGrowth.bounded (abs_nonneg c) (fun _ => le_rfl)

lemma RowExpGrowth.const_mul {v : ℝ → ℝ} (hv : RowExpGrowth v) (c : ℝ) :
    RowExpGrowth (fun x => c*v x) := (rowExpGrowth_const c).mul hv

lemma rowDensity_score_integrable {v : ℝ → ℝ} (hm : Measurable v) (hg : RowExpGrowth v)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    Integrable (fun z => rowHeatDensity T z*(z^2/(2*T^2)-1/(2*T))*v (x+z)) := by
  have hg' := (((rowExpGrowth_pow 2).const_mul (1/(2*T^2))).add
    (rowExpGrowth_const (-(1/(2*T))))).mul (hg.affine x 1)
  have hi := rowDensity_integrable (by fun_prop) hg' hT 0
  convert hi using 1
  funext z
  simp only [zero_add,one_mul]
  ring

 

lemma rowHeat_parameter_derivative
    {f f' : ℝ → ℝ → ℝ} {v₁ v₂ : ℝ → ℝ} {T : ℝ → ℝ} {δ t₀ a b K L : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 t₀) (ha : 0 < a) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hT : ∀ t ∈ s, a ≤ T t ∧ T t ≤ b)
    (hdT : ∀ t ∈ s, HasDerivAt T δ t)
    (hm : ∀ t, Measurable (f t)) (hm' : Measurable (f' t₀))
    (hd : ∀ t ∈ s, ∀ z, HasDerivAt (fun r => f r z) (f' t z) t)
    (hb : ∀ t ∈ s, ∀ z, |f t z| ≤ K*Real.exp (L*|z|) ∧ |f' t z| ≤ K*Real.exp (L*|z|))
    (hv₁ : Measurable v₁) (hv₂ : Measurable v₂) (hg₁ : RowExpGrowth v₁) (hg₂ : RowExpGrowth v₂)
    (hsd : ∀ y, HasDerivAt (f t₀) (v₁ y) y) (hsd₁ : ∀ y, HasDerivAt v₁ (v₂ y) y)
    (x : ℝ) :
    HasDerivAt (fun t => gaussianHeat (f t) (T t) x)
      (gaussianHeat (f' t₀) (T t₀) x + δ/2*gaussianHeat v₂ (T t₀) x) t₀ := by
  have ht₀ := mem_of_mem_nhds hs
  have hT₀ := ha.trans_le (hT t₀ ht₀).1
  have hg : RowExpGrowth (f t₀) := ⟨K,L,hK,hL,fun y => (hb t₀ ht₀ y).1⟩
  have hg' : RowExpGrowth (f' t₀) := ⟨K,L,hK,hL,fun y => (hb t₀ ht₀ y).2⟩
  have he (t) (ht : t ∈ s) : gaussianHeat (f t) (T t) x =
      ∫ z, rowHeatDensity (T t) z*f t (x+z) := gaussianHeat_eq_density (hm t) (ha.trans_le (hT t ht).1) x
  have hh := rowDensity_parameter_derivative (f := fun t z => f t (x+z)) (f' := fun t z => f' t (x+z))
    hs ha (show 0 ≤ K*Real.exp (L*|x|) by positivity) hT hdT
    (fun t => (hm t).comp (by fun_prop)) (hm'.comp (by fun_prop))
    (fun t ht z => hd t ht (x+z)) (fun t ht z => by
      have hx : Real.exp (L*|x+z|) ≤ Real.exp (L*|x|)*Real.exp (L*|z|) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left (abs_add_le x z) hL
        linarith
      constructor <;> calc
        _ ≤ K*Real.exp (L*|x+z|) := by first | exact (hb t ht (x+z)).1 | exact (hb t ht (x+z)).2
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hx hK])
  have hi := rowDensity_integrable hm' hg' hT₀ x
  have hscore := rowDensity_score_integrable (hm t₀) hg hT₀ x
  have hval : (∫ z, rowHeatDensity (T t₀) z*(f' t₀ (x+z)+δ*(z^2/(2*(T t₀)^2)-1/(2*T t₀))*f t₀ (x+z))) =
      gaussianHeat (f' t₀) (T t₀) x + δ/2*gaussianHeat v₂ (T t₀) x := by
    calc
      _ = (∫ z, rowHeatDensity (T t₀) z*f' t₀ (x+z)) +
          δ*(∫ z,rowHeatDensity (T t₀) z*(z^2/(2*(T t₀)^2)-1/(2*T t₀))*f t₀ (x+z)) := by
        rw [← integral_const_mul,← integral_add hi (hscore.const_mul δ)]
        congr 1; funext z; ring
      _ = _ := by
        rw [← gaussianHeat_eq_density hm' hT₀ x,
          rowDensity_score_identity (hm t₀) hv₁ hv₂ hg hg₁ hg₂ hsd hsd₁ hT₀ x]
        ring
  rw [hval] at hh
  exact hh.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem hs (fun t ht => he t ht))
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma rowFamily_linear_envelope {f f' : ℝ → ℝ → ℝ} {L H A C : ℝ} {s : Set ℝ}
    (hf : ∀ t, RowBoundedTerminal (f t) L H) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hv : ∀ t ∈ s, |f t 0| ≤ A) (hb : ∀ t ∈ s, ∀ y, |f' t y| ≤ C) :
    ∀ t ∈ s, ∀ y, |f t y| ≤ (A+L+C)*Real.exp |y| ∧
      |f' t y| ≤ (A+L+C)*Real.exp |y| := by
  intro t ht y
  have hL := (hf t).L_nonneg
  have he : 1 ≤ Real.exp |y| := Real.one_le_exp (abs_nonneg _)
  have he' : |y| ≤ Real.exp |y| := by linarith [Real.add_one_le_exp |y|]
  constructor
  · calc
      _ ≤ |f t 0|+L*|y| := bounded_deriv_linear (hf t).diff (hf t).slope y
      _ ≤ A+L*|y| := add_le_add (hv t ht) le_rfl
      _ ≤ _ := by nlinarith
  · exact (hb t ht y).trans (by nlinarith)

lemma rowFamily_exp_envelope {f f' : ℝ → ℝ → ℝ} {L H A C : ℝ} {s : Set ℝ}
    (hf : ∀ t, RowBoundedTerminal (f t) L H) (_hA : 0 ≤ A) (hC : 0 ≤ C)
    (hv : ∀ t ∈ s, |f t 0| ≤ A) (hb : ∀ t ∈ s, ∀ y, |f' t y| ≤ C) (a : ℝ) :
    ∀ t ∈ s, ∀ y,
      |Real.exp (a*f t y)| ≤ (Real.exp (|a| *A)*(1+|a| *C))*Real.exp ((|a| *L)*|y|) ∧
      |a*f' t y*Real.exp (a*f t y)| ≤
        (Real.exp (|a| *A)*(1+|a| *C))*Real.exp ((|a| *L)*|y|) := by
  intro t ht y
  have hv' : |f t y| ≤ A+L*|y| :=
    (bounded_deriv_linear (hf t).diff (hf t).slope y).trans (add_le_add (hv t ht) le_rfl)
  have he : Real.exp (a*f t y) ≤ Real.exp (|a| *A)*Real.exp ((|a| *L)*|y|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha : a*f t y ≤ |a| *|f t y| := by simpa only [abs_mul] using le_abs_self (a*f t y)
    nlinarith [mul_le_mul_of_nonneg_left hv' (abs_nonneg a)]
  have hh : |a*f' t y| ≤ |a| *C := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb t ht y) (abs_nonneg a)
  constructor
  · rw [abs_of_pos (Real.exp_pos _)]
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg a) hC) (mul_nonneg (Real.exp_pos (|a| *A)).le (Real.exp_pos ((|a| *L)*|y|)).le)]
  · rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (|a| *C)*(Real.exp (|a| *A)*Real.exp ((|a| *L)*|y|)) :=
        mul_le_mul hh he (Real.exp_pos _).le (by positivity)
      _ ≤ _ := by nlinarith [mul_pos (Real.exp_pos (|a| *A)) (Real.exp_pos ((|a| *L)*|y|))]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma rowTiltStep_parameter_zero (T x : ℝ) (f h : ℝ → ℝ) :
    rowTiltStep 0 T f x h = gaussianHeat h T x := by
  simp [rowTiltStep,gaussianHeat]

lemma rowTiltStep_variance_decomposition {f h : ℝ → ℝ} {L H C : ℝ}
    (hf : RowBoundedTerminal f L H) (hm : Measurable h) (hC : 0 ≤ C) (hb : ∀ y, |h y| ≤ C)
    (a T x δ : ℝ) :
    rowTiltStep a T f x (fun y => h y+δ/2*(deriv (deriv f) y+a*(deriv f y)^2)) =
      rowTiltStep a T f x h+δ/2*(rowTiltStep a T f x (deriv (deriv f))+
        a*rowTiltStep a T f x (fun y => (deriv f y)^2)) := by
  have hg := (rowBounded_exp_growth hf a).1
  have hi := rowTiltStep_product_integrable hf.diff.continuous.measurable hg hm hC hb T x
  have hc := rowTiltStep_product_integrable hf.diff.continuous.measurable hg
    (measurable_deriv (deriv f)) hf.H_nonneg hf.curvature T x
  have hb₂ (y) : |(deriv f y)^2| ≤ L^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hf.slope y,sq_abs (deriv f y),abs_nonneg (deriv f y),hf.L_nonneg]
  have hsq := rowTiltStep_product_integrable hf.diff.continuous.measurable hg
    ((measurable_deriv f).pow_const 2) (sq_nonneg L) hb₂ T x
  have hcomb : Integrable (fun z => (deriv (deriv f) (x+Real.sqrt T*z)+a*(deriv f (x+Real.sqrt T*z))^2)*
      Real.exp (a*f (x+Real.sqrt T*z))) (gaussianReal 0 1) := by
    convert hc.add (hsq.const_mul a) using 1
    funext z; dsimp; ring
  have he₁ := rowTiltStep_linear (k := fun y => deriv (deriv f) y+a*(deriv f y)^2) hi hcomb 1 (δ/2)
  have he₂ := rowTiltStep_linear (k := fun y => (deriv f y)^2) hc hsq 1 a
  simp only [one_mul] at he₁ he₂
  rw [he₁,he₂]

lemma rowOperator_parameter_derivative
    {f f' : ℝ → ℝ → ℝ} {T : ℝ → ℝ} {δ t₀ lo hi L H A C : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 t₀) (hlo : 0 < lo) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hT : ∀ t ∈ s, lo ≤ T t ∧ T t ≤ hi)
    (hdT : ∀ t ∈ s, HasDerivAt T δ t)
    (hf : ∀ t, RowBoundedTerminal (f t) L H) (hm' : Measurable (f' t₀))
    (hd : ∀ t ∈ s, ∀ y, HasDerivAt (fun r => f r y) (f' t y) t)
    (hv : ∀ t ∈ s, |f t 0| ≤ A) (hb : ∀ t ∈ s, ∀ y, |f' t y| ≤ C)
    (a x : ℝ) :
    HasDerivAt (fun t => gaussianRowOperator a (T t) (f t) x)
      (rowTiltStep a (T t₀) (f t₀) x (fun y => f' t₀ y+δ/2*
        (deriv (deriv (f t₀)) y+a*(deriv (f t₀) y)^2))) t₀ := by
  have ht₀ := mem_of_mem_nhds hs
  have hL := (hf t₀).L_nonneg
  have hH := (hf t₀).H_nonneg
  have hft := hf t₀
  rw [rowTiltStep_variance_decomposition hft hm' hC (hb t₀ ht₀)]
  by_cases haz : a=0
  · subst a
    simp only [gaussianRowOperator,ite_true,rowTiltStep_parameter_zero,zero_mul,add_zero]
    apply rowHeat_parameter_derivative hs hlo (by positivity : 0 ≤ A+L+C) (by norm_num : (0:ℝ) ≤ 1)
      hT hdT (fun t => (hf t).diff.continuous.measurable) hm' hd
      (by simpa only [one_mul] using rowFamily_linear_envelope hf hA hC hv hb)
      (measurable_deriv (f t₀)) (measurable_deriv (deriv (f t₀)))
      (RowExpGrowth.bounded hL hft.slope) (RowExpGrowth.bounded hH hft.curvature)
      (fun y => (hft.diff y).hasDerivAt) (fun y => (hft.diff_deriv y).hasDerivAt) x
  · obtain ⟨hm,hm₁,hm₂⟩ := rowBounded_exp_measurable hft a
    obtain ⟨hg,hg₁,hg₂⟩ := rowBounded_exp_growth hft a
    obtain ⟨hd₁,hd₂⟩ := rowBounded_exp_derivatives hft a
    have hpd := rowHeat_parameter_derivative (f := fun t y => Real.exp (a*f t y))
      (f' := fun t y => a*f' t y*Real.exp (a*f t y))
      hs hlo (by positivity : 0 ≤ Real.exp (|a| *A)*(1+|a| *C)) (by positivity : 0 ≤ |a| *L)
      hT hdT (fun t => ((hf t).diff.continuous.measurable.const_mul a).exp)
      ((hm'.const_mul a).mul hm)
      (fun t ht y => by convert ((hd t ht y).const_mul a).exp using 1; first | rfl | ring)
      (rowFamily_exp_envelope hf hA hC hv hb a) hm₁ hm₂ hg₁ hg₂ hd₁ hd₂ x
    have hp : gaussianHeat (fun y => Real.exp (a*f t₀ y)) (T t₀) x ≠ 0 :=
      (integral_exp_pos (hg.integrable_affine hm x (Real.sqrt (T t₀)))).ne'
    have hdlog := (hpd.log hp).const_mul (1/a)
    have hresp := rowTiltStep_product_integrable hft.diff.continuous.measurable hg hm' hC (hb t₀ ht₀) (T t₀) x
    have hcurv := rowTiltStep_product_integrable hft.diff.continuous.measurable hg
      (measurable_deriv (deriv (f t₀))) hH hft.curvature (T t₀) x
    have hb₂ (y) : |(deriv (f t₀) y)^2| ≤ L^2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hft.slope y,sq_abs (deriv (f t₀) y),abs_nonneg (deriv (f t₀) y),hL]
    have hsq := rowTiltStep_product_integrable hft.diff.continuous.measurable hg
      ((measurable_deriv (f t₀)).pow_const 2) (sq_nonneg L) hb₂ (T t₀) x
    have hr : gaussianHeat (fun y => a*f' t₀ y*Real.exp (a*f t₀ y)) (T t₀) x =
        a*(∫ z, f' t₀ (x+Real.sqrt (T t₀)*z)*Real.exp (a*f t₀ (x+Real.sqrt (T t₀)*z)) ∂gaussianReal 0 1) := by
      rw [← integral_const_mul]
      unfold gaussianHeat
      congr 1; funext z; ring
    have hc : gaussianHeat (rowBoundedExpSecond a (f t₀)) (T t₀) x =
        a*(∫ z,deriv (deriv (f t₀)) (x+Real.sqrt (T t₀)*z)*Real.exp (a*f t₀ (x+Real.sqrt (T t₀)*z)) ∂gaussianReal 0 1)+
        a^2*(∫ z,(deriv (f t₀) (x+Real.sqrt (T t₀)*z))^2*Real.exp (a*f t₀ (x+Real.sqrt (T t₀)*z)) ∂gaussianReal 0 1) := by
      rw [← integral_const_mul,← integral_const_mul,← integral_add (hcurv.const_mul a) (hsq.const_mul (a^2))]
      unfold gaussianHeat rowBoundedExpSecond
      congr 1; funext z; ring
    simp only [gaussianRowOperator,ite_eq_right haz]
    convert hdlog using 1
    rw [hr,hc]
    unfold rowTiltStep gaussianHeat
    field_simp [haz]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma rowVariance_integrand_bound {f h : ℝ → ℝ} {L H C a δ : ℝ}
    (hf : RowBoundedTerminal f L H) (hh : ∀ y, |h y| ≤ C) (ha : 0 ≤ a) (ha1 : a ≤ 1) (y : ℝ) :
    |h y+δ/2*(deriv (deriv f) y+a*(deriv f y)^2)| ≤ C+|δ|/2*(H+L^2) := by
  have hd : (deriv f y)^2 ≤ L^2 := by
    nlinarith [hf.slope y,sq_abs (deriv f y),abs_nonneg (deriv f y),hf.L_nonneg]
  have hb : |deriv (deriv f) y+a*(deriv f y)^2| ≤ H+L^2 := by
    calc
      _ ≤ |deriv (deriv f) y|+|a*(deriv f y)^2| := abs_add_le _ _
      _ ≤ H+a*(deriv f y)^2 := by
        rw [abs_of_nonneg (mul_nonneg ha (sq_nonneg _))]
        exact add_le_add (hf.curvature y) le_rfl
      _ ≤ _ := by nlinarith [sq_nonneg (deriv f y)]
  calc
    _ ≤ |h y|+|δ/2*(deriv (deriv f) y+a*(deriv f y)^2)| := abs_add_le _ _
    _ = |h y|+|δ|/2*|deriv (deriv f) y+a*(deriv f y)^2| := by rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    _ ≤ _ := add_le_add (hh y) (mul_le_mul_of_nonneg_left hb (by positivity))

 

lemma rowVarianceFamily_bounds {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (bs : List (ℝ × ℝ × ℝ)) (hbs : ∀ b ∈ bs, 0 ≤ b.1 ∧ b.1 ≤ 1) :
    ∃ K C : ℝ, 0 ≤ C ∧
      (∀ t, RowBoundedTerminal (gaussianRowComposition (rowInterpolatedBlocks bs t) u) L K) ∧
      (∀ t, Measurable (rowFiniteVarianceResponse bs u t)) ∧
      (∀ t x, |rowFiniteVarianceResponse bs u t x| ≤ C) := by
  induction bs with
  | nil =>
    refine ⟨H,0,le_rfl,?_,?_,?_⟩
    · intro t; exact hu
    · intro t; exact measurable_const
    · intro t x; simp [rowFiniteVarianceResponse]
  | cons b bs ih =>
    rcases b with ⟨a,T,R⟩
    have ha := hbs (a,T,R) List.mem_cons_self
    obtain ⟨K,C,hC,hf,hm,hb⟩ := ih (fun c hc => hbs c (List.mem_cons_of_mem _ hc))
    let B := C+|R-T|/2*(K+L^2)
    have hK : 0 ≤ K := (hf 0).H_nonneg
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hmi (t : ℝ) : Measurable (fun y => rowFiniteVarianceResponse bs u t y+(R-T)/2*
        (deriv (deriv (gaussianRowComposition (rowInterpolatedBlocks bs t) u)) y+
          a*(deriv (gaussianRowComposition (rowInterpolatedBlocks bs t) u) y)^2)) :=
      (hm t).add ((((measurable_deriv (deriv _)).add ((measurable_deriv _).pow_const 2 |>.const_mul a))).const_mul ((R-T)/2))
    refine ⟨K+2*L^2,B,hB,?_,?_,?_⟩
    · intro t
      exact rowBoundedOperator_terminal (hf t) ha.1 ha.2 ((1-t)*T+t*R)
    · intro t
      exact measurable_rowTiltStep (hf t).diff.continuous.measurable (hmi t) a ((1-t)*T+t*R)
    · intro t x
      exact rowTiltStep_abs_bound (hf t).diff.continuous.measurable (rowBounded_exp_growth (hf t) a).1
        (hmi t) hB (rowVariance_integrand_bound (hf t) (hb t) ha.1 ha.2) ((1-t)*T+t*R) x
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma rowFiniteVariance_of_bounded {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (bs : List (ℝ × ℝ × ℝ))
    (hbs : ∀ b ∈ bs, 0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2.1 ∧ 0 ≤ b.2.2) :
    ∀ t ∈ Set.Ioo (0:ℝ) 1, ∀ x,
      HasDerivAt (fun s => gaussianRowComposition (rowInterpolatedBlocks bs s) u x)
        (rowFiniteVarianceResponse bs u t x) t := by
  induction bs with
  | nil =>
    intro t ht x
    exact hasDerivAt_const t (u x)
  | cons b bs ih =>
    rcases b with ⟨a,T,R⟩
    have ha := hbs (a,T,R) List.mem_cons_self
    have htail := fun c hc => hbs c (List.mem_cons_of_mem (a,T,R) hc)
    have hi := ih htail
    intro t ht x
    by_cases hz : T=0 ∧ R=0
    · rcases hz with ⟨rfl,rfl⟩
      simpa only [rowInterpolatedBlocks,List.map_cons,gaussianRowComposition,
        mul_zero,zero_add,rowFiniteVarianceResponse,sub_self,zero_div,zero_mul,add_zero,
        gaussianRowOperator_zero,rowTiltStep_zero] using hi t ht x
    · have hvar : 0 < (1-t)*T+t*R := by
        by_cases hT : T=0
        · have hR : 0 < R := lt_of_le_of_ne ha.2.2.2 (by intro h; exact hz ⟨hT,h.symm⟩)
          have := mul_pos ht.1 hR
          simpa [hT] using this
        · have hT' : 0 < T := lt_of_le_of_ne ha.2.2.1 (Ne.symm hT)
          have := mul_pos (show 0 < 1-t by linarith [ht.2]) hT'
          have := mul_nonneg ht.1.le ha.2.2.2
          linarith
      obtain ⟨K,C,hC,hf,hm,hb⟩ := rowVarianceFamily_bounds hu bs (fun c hc => ⟨(htail c hc).1,(htail c hc).2.1⟩)
      let V : ℝ → ℝ := fun s => (1-s)*T+s*R
      let A := |gaussianRowComposition (rowInterpolatedBlocks bs t) u 0|+1
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hcV : Continuous V := by dsimp [V]; fun_prop
      have hnearV : ∀ᶠ s in 𝓝 t, V t/2 < V s ∧ V s < V t+1 :=
        hcV.continuousAt.eventually (Ioo_mem_nhds (by dsimp [V]; linarith) (by linarith))
      have hcF := (hi t ht 0).continuousAt.abs
      have hnearF : ∀ᶠ s in 𝓝 t, |gaussianRowComposition (rowInterpolatedBlocks bs s) u 0| < A :=
        hcF.eventually (Iio_mem_nhds (by dsimp [A]; linarith))
      let s : Set ℝ := {r | r ∈ Set.Ioo (0:ℝ) 1 ∧ (V t/2 < V r ∧ V r < V t+1) ∧
        |gaussianRowComposition (rowInterpolatedBlocks bs r) u 0| < A}
      have hs : s ∈ 𝓝 t := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2,hnearV,hnearF] with r hr hV hF
        exact ⟨hr,hV,hF⟩
      have hdV (r : ℝ) : HasDerivAt V (R-T) r := by
        convert (((hasDerivAt_const r 1).sub (hasDerivAt_id r)).mul_const T).add ((hasDerivAt_id r).mul_const R) using 1
        <;> first | rfl | ring
      have hh := rowOperator_parameter_derivative hs (by dsimp [V]; linarith : 0 < V t/2) hA hC
        (fun r hr => ⟨hr.2.1.1.le,hr.2.1.2.le⟩) (fun r _ => hdV r) hf (hm t)
        (fun r hr y => hi r hr.1 y) (fun r hr => hr.2.2.le) (fun r _ y => hb r y) a x
      exact hh

theorem rowFiniteVariance : RowFiniteVarianceStatement := by
  intro u L H hu hL hH hb bs hbs t ht x
  apply rowFiniteVariance_of_bounded (L := L) (H := H) ?_ bs hbs t ht x
  have hud : ContDiff ℝ 1 (deriv u) := hu.deriv'
  exact ⟨hu.differentiable (by norm_num),
    hud.differentiable (by norm_num),hL,hH,
    fun y => (hb y).1,fun y => (hb y).2⟩
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma rowInterpolatedBlocks_valid {bs : List (ℝ × ℝ × ℝ)}
    (hbs : ∀ b ∈ bs, 0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2.1 ∧ 0 ≤ b.2.2)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∀ r ∈ rowInterpolatedBlocks bs t, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2 := by
  intro r hr
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hr
  have hb' := hbs b hb
  exact ⟨hb'.1,hb'.2.1,add_nonneg (mul_nonneg (by linarith [ht.2]) hb'.2.2.1)
    (mul_nonneg ht.1 hb'.2.2.2)⟩

lemma rowDepthPairing_measurable {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (rs : List (ℝ × ℝ)) (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (cs : List ℝ) (j : ℕ) : Measurable (rowDepthPairing rs u cs j) := by
  induction cs generalizing j with
  | nil => exact measurable_const
  | cons c cs ih => exact ((measurable_rowDerivativeDepthMoment hu rs hrs j).const_mul c).add (ih (j+1))

lemma rowDepthPairing_bound {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (rs : List (ℝ × ℝ)) (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (cs : List ℝ) (j : ℕ) (x : ℝ) :
    |rowDepthPairing rs u cs j x| ≤ (cs.map abs).sum*L^2 := by
  induction cs generalizing j with
  | nil => simp [rowDepthPairing]
  | cons c cs ih =>
    have hb := rowDerivativeDepthMoment_bounds hu rs hrs j x
    simp only [rowDepthPairing,List.map_cons,List.sum_cons]
    calc
      _ ≤ |c*rowDerivativeDepthMoment rs u j x|+|rowDepthPairing rs u cs (j+1) x| := abs_add_le _ _
      _ ≤ |c| *L^2+(cs.map abs).sum*L^2 := by
        rw [abs_mul,abs_of_nonneg hb.1]
        exact add_le_add (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg c)) (ih (j+1))
      _ = _ := by ring

lemma rowDepthPairing_tilt {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (rs : List (ℝ × ℝ)) (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (a T : ℝ) (cs : List ℝ) (j : ℕ) (x : ℝ) :
    rowDepthPairing ((a,T)::rs) u cs (j+1) x =
      rowTiltStep a T (gaussianRowComposition rs u) x (rowDepthPairing rs u cs j) := by
  obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hu rs hrs
  have hg := (rowBounded_exp_growth hK a).1
  induction cs generalizing j with
  | nil => simp [rowDepthPairing,rowTiltStep]
  | cons c cs ih =>
    have hb (y) : |rowDerivativeDepthMoment rs u j y| ≤ L^2 := by
      rw [abs_of_nonneg (rowDerivativeDepthMoment_bounds hu rs hrs j y).1]
      exact (rowDerivativeDepthMoment_bounds hu rs hrs j y).2
    have hd := rowTiltStep_product_integrable hK.diff.continuous.measurable hg
      (measurable_rowDerivativeDepthMoment hu rs hrs j) (sq_nonneg L) hb T x
    have hp := rowTiltStep_product_integrable hK.diff.continuous.measurable hg
      (rowDepthPairing_measurable hu rs hrs cs (j+1))
      (mul_nonneg (List.sum_nonneg (fun c hc => by obtain ⟨d,_,rfl⟩ := List.mem_map.mp hc; exact abs_nonneg d)) (sq_nonneg L))
      (rowDepthPairing_bound hu rs hrs cs (j+1)) T x
    simp only [rowDepthPairing,rowDerivativeDepthMoment,ih]
    have he := rowTiltStep_linear hd hp c 1
    simpa only [one_mul] using he.symm
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace MicroscopicJamming
def gaussianRankProfile (rs : List (ℝ × ℝ)) (s : ℝ) : ℝ :=
  (rs.map (fun r => if r.1 ≤ s then r.2 else 0)).sum
def RowFiniteIntegralStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
    ∀ bs : List (ℝ × ℝ × ℝ),
      (∀ c ∈ bs, 0 ≤ c.1 ∧ c.1 ≤ 1 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2) →
      bs.Pairwise (fun c d => c.1 ≤ d.1) → rowVarianceTotal bs=0 →
      ∀ t ∈ Set.Ioo (0:ℝ) 1, ∀ x : ℝ,
        HasDerivAt (fun s => gaussianRowComposition (rowInterpolatedBlocks bs s) u x)
          (-(1/2:ℝ)*(∫ s in (0:ℝ)..1,
            (gaussianRankProfile (bs.map (fun c => (c.1,c.2.2))) s-
             gaussianRankProfile (bs.map (fun c => (c.1,c.2.1))) s)*
             rowDerivativeRankMoment (rowInterpolatedBlocks bs t) u s x)) t
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

namespace MicroscopicJamming

lemma gaussianRankProfile_cons (r : ℝ × ℝ) (rs : List (ℝ × ℝ)) (s : ℝ) :
    gaussianRankProfile (r::rs) s = (if r.1 ≤ s then r.2 else 0)+gaussianRankProfile rs s := by
  simp [gaussianRankProfile]

lemma measurable_gaussianRankProfile (rs : List (ℝ × ℝ)) : Measurable (gaussianRankProfile rs) := by
  induction rs with
  | nil => exact measurable_const
  | cons r rs ih =>
    change Measurable (fun s => (if r.1 ≤ s then r.2 else 0)+gaussianRankProfile rs s)
    exact (Measurable.ite (measurableSet_Ici) measurable_const measurable_const).add ih

lemma gaussianRankProfile_bound (rs : List (ℝ × ℝ)) (s : ℝ) :
    |gaussianRankProfile rs s| ≤ (rs.map (fun r => |r.2|)).sum := by
  induction rs with
  | nil => simp [gaussianRankProfile]
  | cons r rs ih =>
    rw [gaussianRankProfile_cons]
    simp only [List.map_cons,List.sum_cons]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    split_ifs <;> simp [abs_nonneg]

lemma measurable_rowRankSelect (as : List ℝ) (M : ℕ → ℝ) (j : ℕ) :
    Measurable (rowRankSelect as M j) := by
  induction as generalizing j with
  | nil => exact measurable_const
  | cons a as ih => exact Measurable.ite measurableSet_Iio measurable_const (ih (j+1))

lemma rowRankSelect_bound (as : List ℝ) (M : ℕ → ℝ) (j : ℕ) (s : ℝ) :
    |rowRankSelect as M j s| ≤ ∑ i ∈ Finset.range (as.length+1), |M (j+i)| := by
  induction as generalizing j with
  | nil => simp [rowRankSelect]
  | cons a as ih =>
    simp only [rowRankSelect]
    rw [List.length_cons,Finset.sum_range_succ']
    simp only [Nat.add_zero]
    split_ifs with h
    · exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    · have he : (∑ i ∈ Finset.range (as.length+1), |M ((j+1)+i)|) =
          ∑ i ∈ Finset.range (as.length+1), |M (j+(i+1))| := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 2; omega
      exact (ih (j+1)).trans (by rw [he]; exact le_add_of_nonneg_right (abs_nonneg _))

lemma rowRankProduct_intervalIntegrable (ts rs : List (ℝ × ℝ)) (as : List ℝ)
    (M : ℕ → ℝ) (j : ℕ) (S a b : ℝ) :
    IntervalIntegrable (fun s => (gaussianRankProfile rs s-gaussianRankProfile ts s-S)*rowRankSelect as M j s)
      volume a b := by
  rw [intervalIntegrable_iff]
  let : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) := by
    change IsFiniteMeasure (volume.restrict (Set.Ioc (min a b) (max a b)))
    infer_instance
  let C := ((rs.map (fun r => |r.2|)).sum+(ts.map (fun r => |r.2|)).sum+|S|)
  let K := ∑ i ∈ Finset.range (as.length+1), |M (j+i)|
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (add_nonneg (List.sum_nonneg (fun y hy => by obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hy; exact abs_nonneg _)) (List.sum_nonneg (fun y hy => by obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hy; exact abs_nonneg _))) (abs_nonneg S)
  apply (integrable_const (C*K)).mono'
    ((((measurable_gaussianRankProfile rs).sub (measurable_gaussianRankProfile ts)).sub measurable_const).mul
      (measurable_rowRankSelect as M j)).aestronglyMeasurable
  apply Eventually.of_forall
  intro s
  change |(gaussianRankProfile rs s-gaussianRankProfile ts s-S)*rowRankSelect as M j s| ≤ C*K
  rw [abs_mul]
  apply mul_le_mul ?_ (rowRankSelect_bound as M j s) (abs_nonneg _) hC
  have h₁ := abs_add_le (gaussianRankProfile rs s) (-gaussianRankProfile ts s)
  have h₂ := abs_add_le (gaussianRankProfile rs s-gaussianRankProfile ts s) (-S)
  simp only [abs_neg,← sub_eq_add_neg] at h₁ h₂
  dsimp [C]
  linarith [gaussianRankProfile_bound rs s,gaussianRankProfile_bound ts s]

lemma gaussianRankProfile_before (rs : List (ℝ × ℝ)) {s : ℝ}
    (hs : ∀ r ∈ rs, s < r.1) : gaussianRankProfile rs s = 0 := by
  unfold gaussianRankProfile
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hy
  simp [not_le.mpr (hs r hr)]

lemma rowRankIntegral_pairing (bs : List (ℝ × ℝ × ℝ))
    (hord : bs.Pairwise (fun c d => c.1 ≤ d.1))
    (hupper : ∀ c ∈ bs, c.1 ≤ 1) (b : ℝ) (hlower : ∀ c ∈ bs, b ≤ c.1)
    (rs : List (ℝ × ℝ)) (u : ℝ → ℝ) (j : ℕ) (x : ℝ) :
    (∫ s in b..1, (gaussianRankProfile (bs.map (fun c => (c.1,c.2.2))) s-
      gaussianRankProfile (bs.map (fun c => (c.1,c.2.1))) s-rowVarianceTotal bs)*
      rowRankSelect (bs.map Prod.fst) (fun k => rowDerivativeDepthMoment rs u k x) j s) =
      -2*rowDepthPairing rs u (rowVarianceCoefficients bs b) j x := by
  induction bs generalizing b j with
  | nil => simp [gaussianRankProfile,rowVarianceTotal,rowVarianceCoefficients,rowDepthPairing]
  | cons c bs ih =>
    rcases c with ⟨a,T,R⟩
    have hba : b ≤ a := hlower (a,T,R) (by simp)
    have ha1 : a ≤ 1 := hupper (a,T,R) (by simp)
    have htail := (List.pairwise_cons.mp hord).1
    let M := fun k => rowDerivativeDepthMoment rs u k x
    let ts := bs.map (fun c => (c.1,c.2.1))
    let vs := bs.map (fun c => (c.1,c.2.2))
    let S := rowVarianceTotal ((a,T,R)::bs)
    have hleft : (∫ s in b..a, (gaussianRankProfile ((a,R)::vs) s-gaussianRankProfile ((a,T)::ts) s-S)*
        rowRankSelect (a::bs.map Prod.fst) M j s) = (a-b)*(-S*M j) := by
      calc
        _ = ∫ _ in b..a, -S*M j := intervalIntegral.integral_congr_Ioo_of_le hba (fun s hs => by
          have ht : ∀ r ∈ (a,T)::ts, s < r.1 := by
            intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · exact hs.2
            · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
              exact hs.2.trans_le (htail c hc)
          have hv : ∀ r ∈ (a,R)::vs, s < r.1 := by
            intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · exact hs.2
            · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
              exact hs.2.trans_le (htail c hc)
          rw [gaussianRankProfile_before _ ht,gaussianRankProfile_before _ hv]
          simp [rowRankSelect,hs.2])
        _ = _ := by simp only [intervalIntegral.integral_const,smul_eq_mul]
    have hright : (∫ s in a..1, (gaussianRankProfile ((a,R)::vs) s-gaussianRankProfile ((a,T)::ts) s-S)*
        rowRankSelect (a::bs.map Prod.fst) M j s) =
        ∫ s in a..1, (gaussianRankProfile vs s-gaussianRankProfile ts s-rowVarianceTotal bs)*
          rowRankSelect (bs.map Prod.fst) M (j+1) s := by
      apply intervalIntegral.integral_congr_Ioo_of_le ha1
      intro s hs
      simp only [gaussianRankProfile_cons,ite_eq_left hs.1.le,rowRankSelect,ite_eq_right (not_lt.mpr hs.1.le)]
      dsimp [S,rowVarianceTotal]
      simp only [List.map_cons,List.sum_cons]
      ring
    change (∫ s in b..1, (gaussianRankProfile ((a,R)::vs) s-gaussianRankProfile ((a,T)::ts) s-S)*
      rowRankSelect (a::bs.map Prod.fst) M j s) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (rowRankProduct_intervalIntegrable ((a,T)::ts) ((a,R)::vs) (a::bs.map Prod.fst) M j S b a)
      (rowRankProduct_intervalIntegrable ((a,T)::ts) ((a,R)::vs) (a::bs.map Prod.fst) M j S a 1),hleft,hright]
    rw [ih (List.pairwise_cons.mp hord).2 (fun c hc => hupper c (List.mem_cons_of_mem _ hc)) a htail (j+1)]
    simp only [rowVarianceCoefficients,rowDepthPairing]
    dsimp [S,M]
    ring
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma rowVarianceTotal_cons (a T R : ℝ) (bs : List (ℝ × ℝ × ℝ)) :
    rowVarianceTotal ((a,T,R)::bs) = (R-T)+rowVarianceTotal bs := by
  simp [rowVarianceTotal]

lemma rowFiniteVarianceResponse_diagonal {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (bs : List (ℝ × ℝ × ℝ))
    (hbs : ∀ c ∈ bs, 0 ≤ c.1 ∧ c.1 ≤ 1 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (b x : ℝ) :
    rowFiniteVarianceResponse bs u t x =
      rowVarianceTotal bs/2*(deriv (deriv (gaussianRowComposition (rowInterpolatedBlocks bs t) u)) x+
        b*(deriv (gaussianRowComposition (rowInterpolatedBlocks bs t) u) x)^2)+
      rowDepthPairing (rowInterpolatedBlocks bs t) u (rowVarianceCoefficients bs b) 0 x := by
  induction bs generalizing b x with
  | nil => simp [rowFiniteVarianceResponse,rowVarianceTotal,rowVarianceCoefficients,rowDepthPairing]
  | cons c bs ih =>
    rcases c with ⟨a,T,R⟩
    have htail := fun c hc => hbs c (List.mem_cons_of_mem (a,T,R) hc)
    let rs := rowInterpolatedBlocks bs t
    let g := gaussianRowComposition rs u
    let V := (1-t)*T+t*R
    let S := rowVarianceTotal bs
    let cs := rowVarianceCoefficients bs a
    have hrs := rowInterpolatedBlocks_valid htail ht
    obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hu rs hrs
    have hg := (rowBounded_exp_growth hK a).1
    have hc := rowTiltStep_product_integrable hK.diff.continuous.measurable hg
      (measurable_deriv (deriv g)) hK.H_nonneg hK.curvature V x
    have hb₂ (y) : |(deriv g y)^2| ≤ L^2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hK.slope y,sq_abs (deriv g y),abs_nonneg (deriv g y),hu.L_nonneg]
    have hsq := rowTiltStep_product_integrable hK.diff.continuous.measurable hg
      ((measurable_deriv g).pow_const 2) (sq_nonneg L) hb₂ V x
    have hcomb : Integrable (fun z => (deriv (deriv g) (x+Real.sqrt V*z)+a*(deriv g (x+Real.sqrt V*z))^2)*
        Real.exp (a*g (x+Real.sqrt V*z))) (gaussianReal 0 1) := by
      convert hc.add (hsq.const_mul a) using 1
      funext z; dsimp; ring
    have hp := rowTiltStep_product_integrable hK.diff.continuous.measurable hg
      (rowDepthPairing_measurable hu rs hrs cs 0)
      (mul_nonneg (List.sum_nonneg (fun c hc => by obtain ⟨d,_,rfl⟩ := List.mem_map.mp hc; exact abs_nonneg d)) (sq_nonneg L))
      (rowDepthPairing_bound hu rs hrs cs 0) V x
    have hin : (fun y => rowFiniteVarianceResponse bs u t y+(R-T)/2*(deriv (deriv g) y+a*(deriv g y)^2)) =
        (fun y => ((R-T)+S)/2*(deriv (deriv g) y+a*(deriv g y)^2)+rowDepthPairing rs u cs 0 y) := by
      funext y
      rw [ih htail a y]
      dsimp [g,rs,S,cs]
      ring
    have hlin := rowTiltStep_linear (h := fun y => deriv (deriv g) y+a*(deriv g y)^2)
      hcomb hp (((R-T)+S)/2) 1
    have hlin' := rowTiltStep_linear (k := fun y => (deriv g y)^2) hc hsq 1 a
    simp only [one_mul] at hlin hlin'
    have hd := rowBoundedOperator_derivatives hK a V
    have hd₁ := (hd.1 x).deriv
    have hd₂ := (hd.2 x).deriv
    change rowTiltStep a V g x (fun y => rowFiniteVarianceResponse bs u t y+(R-T)/2*(deriv (deriv g) y+a*(deriv g y)^2)) = _
    rw [hin,hlin,hlin']
    simp only [rowVarianceCoefficients,rowDepthPairing,rowVarianceTotal_cons,
      rowInterpolatedBlocks,List.map_cons,gaussianRowComposition,rowDerivativeDepthMoment]
    change _ = ((R-T)+S)/2*(deriv (deriv (gaussianRowOperator a V g)) x+b*(deriv (gaussianRowOperator a V g) x)^2)+
      (((R-T)+S)/2*(a-b)*(deriv (gaussianRowOperator a V g) x)^2+
        rowDepthPairing ((a,V)::rs) u cs 1 x)
    rw [rowDepthPairing_tilt hu rs hrs a V cs 0 x,hd₁,hd₂]
    ring

theorem rowFiniteDiagonal : RowFiniteDiagonalStatement := by
  intro u L H hu hL hH hb bs hbs t ht b x
  have hud : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hbu : RowBoundedTerminal u L H := ⟨hu.differentiable (by norm_num),hud.differentiable (by norm_num),
    hL,hH,fun y => (hb y).1,fun y => (hb y).2⟩
  rw [← rowFiniteVarianceResponse_diagonal hbu bs hbs ⟨ht.1.le,ht.2.le⟩ b x]
  exact rowFiniteVariance u L H hu hL hH hb bs hbs t ht x
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace MicroscopicJamming

theorem rowFiniteIntegral : RowFiniteIntegralStatement := by
  intro u L H hu hL hH hb bs hbs hord htotal t ht x
  have hd := rowFiniteDiagonal u L H hu hL hH hb bs hbs t ht 0 x
  simp only [htotal,zero_div,zero_mul,zero_add] at hd
  have hi := rowRankIntegral_pairing bs hord (fun c hc => (hbs c hc).2.1) 0
    (fun c hc => (hbs c hc).1) (rowInterpolatedBlocks bs t) u 0 x
  have hmap : (rowInterpolatedBlocks bs t).map Prod.fst = bs.map Prod.fst := by
    simp [rowInterpolatedBlocks,List.map_map,Function.comp_def]
  simp only [htotal,sub_zero] at hi
  dsimp [rowDerivativeRankMoment]
  rw [hmap,hi]
  convert hd using 1; first | rfl | ring
end MicroscopicJamming

end

end OAI
