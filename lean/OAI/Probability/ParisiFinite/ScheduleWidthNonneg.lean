import Mathlib
import OAI.Probability.ParisiFinite.DyadicEvolutionGridBound

namespace OAI

/-! Schedule Width Nonneg. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set MeasurableSpace
open scoped BigOperators Topology NNReal ENNReal MatrixOrder
open scoped BigOperators Topology NNReal ENNReal ContDiff
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
namespace ParisiFinite

lemma schedule_width_nonneg (ls : Schedule) : 0 ≤ width ls := by
  induction ls with
  | nil => simp [width]
  | cons l ls ih => simpa only [width,List.map_cons,List.sum_cons] using add_nonneg l.2.coe_nonneg ih

 

lemma evolution_lyapunov (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1 ≤ β) (hd : width ls ≤ 1) (x : ℝ) :
    Integrable (fun y : ℝ => 1+y^2) (evolutionKernel β hβ ls x) ∧
    (∫ y,1+y^2 ∂evolutionKernel β hβ ls x) ≤
      Real.exp ((2+2*(β:ℝ)^2)*width ls)*(1+x^2) := by
  induction ls generalizing x with
  | nil =>
    constructor
    · exact integrable_dirac (by simp)
    · simp [evolutionKernel,Kernel.id_apply,width]
  | cons l ls ih =>
    have hw : width (l::ls)=(l.2:ℝ)+width ls := by simp [width]
    have hat : ∀ k∈ls,k.1 ≤ β := fun k hk => ha k (List.mem_cons_of_mem _ hk)
    have hdt : width ls ≤ 1 := by rw [hw] at hd; linarith [l.2.coe_nonneg]
    have hdl : l.2 ≤ 1 := by rw [hw] at hd; exact_mod_cast (by linarith [schedule_width_nonneg ls] : (l.2:ℝ)≤1)
    have hlt := smoothRecursion_hasParisiCurvature β hβ ls hat
    let K := transitionKernel (smoothRecursion β hβ ls) l.1 (Real.sqrt l.2)
    let C := Real.exp ((2+2*(β:ℝ)^2)*width ls)
    have hi : Integrable (fun y : ℝ => 1+y^2) (K x) := by
      rw [show K x=transitionMeasure (smoothRecursion β hβ ls) l.1 (Real.sqrt l.2) x from transitionKernel_apply _ _ _ x]
      exact (integrable_const (1:ℝ)).add (integrable_transition_sq _ _ _ _)
    have hmc : StronglyMeasurable (fun y : ℝ => ∫ z,1+z^2 ∂evolutionKernel β hβ ls y) :=
      (by fun_prop : StronglyMeasurable (fun z : ℝ => 1+z^2)).integral_kernel
    have hib : Integrable (fun y : ℝ => ∫ z,1+z^2 ∂evolutionKernel β hβ ls y) (K x) := by
      apply (hi.const_mul C).mono' hmc.aestronglyMeasurable
      exact ae_of_all _ fun y => by
        rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun z => by positivity))]
        exact (ih hat hdt y).2
    have hI : Integrable (fun y : ℝ => 1+y^2) ((evolutionKernel β hβ ls ∘ₖ K) x) := by
      apply (integrable_comp_iff (by fun_prop)).mpr
      refine ⟨ae_of_all _ fun y => (ih hat hdt y).1,?_⟩
      have he (y : ℝ) : |1+y^2|=1+y^2 := abs_of_nonneg (by positivity)
      simpa only [Real.norm_eq_abs,he] using hib
    refine ⟨hI,?_⟩
    change (∫ y,1+y^2 ∂(evolutionKernel β hβ ls ∘ₖ K) x) ≤ _
    rw [Kernel.integral_comp hI]
    have hh := integral_mono hib (hi.const_mul C) (fun y => (ih hat hdt y).2)
    rw [integral_const_mul] at hh
    have hb := transition_lyapunov_bound hlt l.1.coe_nonneg (by exact_mod_cast ha l (List.mem_cons_self)) hdl x
    rw [←transitionKernel_apply] at hb
    have hfinal := hh.trans (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)
    have he : C*(Real.exp ((2+2*(β:ℝ)^2)*l.2)*(1+x^2))=
        Real.exp ((2+2*(β:ℝ)^2)*width (l::ls))*(1+x^2) := by
      dsimp [C]
      rw [hw,←mul_assoc,←Real.exp_add]
      congr 2
      ring
    rw [←he]
    exact hfinal

lemma integrable_smooth_d2 (f : SmoothField) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable f.d2 μ := by
  exact (integrable_const (f.bound2:ℝ)).mono' f.continuousD2.aestronglyMeasurable
    (ae_of_all _ fun x => f.normD2 x)

 
lemma evolution_terminal_curvature_le (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (x : ℝ) :
    (∫ y,(terminalField β hβ).d2 y ∂evolutionKernel β hβ ls x) ≤
      (smoothRecursion β hβ ls).d2 x := by
  induction ls generalizing x with
  | nil => simp [evolutionKernel,Kernel.id_apply,smoothRecursion]
  | cons l ls ih =>
    let K := transitionKernel (smoothRecursion β hβ ls) l.1 (Real.sqrt l.2)
    have hi := integrable_smooth_d2 (terminalField β hβ) ((evolutionKernel β hβ ls ∘ₖ K) x)
    change (∫ y,(terminalField β hβ).d2 y ∂(evolutionKernel β hβ ls ∘ₖ K) x) ≤ _
    rw [Kernel.integral_comp hi]
    have hh := integral_mono hi.integral_comp (integrable_smooth_d2 (smoothRecursion β hβ ls) (K x)) (fun y => ih y)
    have he := transition_integral (smoothRecursion β hβ ls) l.1 (Real.sqrt l.2) x
      (smoothRecursion β hβ ls).continuousD2.measurable
    rw [←transitionKernel_apply] at he
    rw [show (∫ y,(smoothRecursion β hβ ls).d2 y ∂K x)=_ from he] at hh
    apply hh.trans
    change _ ≤ _+(l.1:ℝ)*_
    apply le_add_of_nonneg_right
    apply mul_nonneg l.1.coe_nonneg
    exact sub_nonneg.mpr (tiltedMean_variance_nonneg (smoothRecursion β hβ ls).lipschitz
      (smoothRecursion β hβ ls).continuousD1 (smoothRecursion β hβ ls).normD1 _ _ _)

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
namespace ParisiFinite

lemma terminal_curvature_minorant (β : ℝ≥0) (hβ : 0<β) {R : ℝ} (hR : 0<R) (y : ℝ) :
    ((β:ℝ)/Real.cosh ((β:ℝ)*R)^2)*(1-y^2/R^2) ≤ (terminalField β hβ).d2 y := by
  change _ ≤ (β:ℝ)/Real.cosh ((β:ℝ)*y)^2
  have hc : 0≤(β:ℝ)/Real.cosh ((β:ℝ)*R)^2 := by positivity
  by_cases hy : |y|≤R
  · have hco := Real.cosh_le_cosh.mpr (show |(β:ℝ)*y|≤|(β:ℝ)*R| from by
      rw [abs_mul,abs_mul,abs_of_nonneg β.coe_nonneg,abs_of_pos hR]
      exact mul_le_mul_of_nonneg_left hy β.coe_nonneg)
    have hco2 : Real.cosh ((β:ℝ)*y)^2≤Real.cosh ((β:ℝ)*R)^2 := by
      nlinarith [Real.cosh_pos ((β:ℝ)*y),Real.cosh_pos ((β:ℝ)*R)]
    have hh := div_le_div_of_nonneg_left β.coe_nonneg (by positivity : 0<Real.cosh ((β:ℝ)*y)^2) hco2
    exact (mul_le_of_le_one_right hc (sub_le_self _ (by positivity))).trans hh
  · have hy2 : R^2≤y^2 := by
      have hyy := (not_le.mp hy).le
      nlinarith [sq_abs y,abs_nonneg y]
    have hh : 1-y^2/R^2≤0 := by
      have hp : 0<R^2 := sq_pos_of_pos hR
      have h1 : 1≤y^2/R^2 := (le_div_iff₀ hp).mpr (by simpa using hy2)
      linarith
    exact (mul_nonpos_of_nonneg_of_nonpos hc hh).trans (by positivity)

lemma finite_curvature_lower (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1 ≤ β) (hd : width ls ≤ 1) (x : ℝ)
    {R : ℝ} (hR : 0<R) (hRx : 2*Real.exp (2+2*(β:ℝ)^2)*(1+x^2) ≤ R^2) :
    (β:ℝ)/(2*Real.cosh ((β:ℝ)*R)^2) ≤ (smoothRecursion β hβ ls).d2 x := by
  let μ := evolutionKernel β hβ ls x
  obtain ⟨hI,hB⟩ := evolution_lyapunov β hβ ls ha hd x
  have hsq : Integrable (fun y : ℝ => y^2) μ := by
    exact (hI.sub (integrable_const (1:ℝ))).congr (ae_of_all _ fun y => by simp)
  have hminor : Integrable (fun y : ℝ => ((β:ℝ)/Real.cosh ((β:ℝ)*R)^2)*(1-y^2/R^2)) μ :=
    ((integrable_const (1:ℝ)).sub (hsq.div_const (R^2))).const_mul _
  have hle := integral_mono hminor (integrable_smooth_d2 (terminalField β hβ) μ)
    (terminal_curvature_minorant β hβ hR)
  rw [integral_const_mul,integral_sub (integrable_const (1:ℝ)) (hsq.div_const (R^2)),integral_div,
    integral_const,probReal_univ,one_smul] at hle
  have hb1 : (∫ y,y^2 ∂μ) ≤ Real.exp (2+2*(β:ℝ)^2)*(1+x^2) := by
    have ht : Real.exp ((2+2*(β:ℝ)^2)*width ls) ≤ Real.exp (2+2*(β:ℝ)^2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (β:ℝ)])
    have hh := hB.trans (mul_le_mul_of_nonneg_right ht (by positivity))
    rw [integral_add (integrable_const (1:ℝ)) hsq,integral_const,probReal_univ,one_smul] at hh
    dsimp [μ]
    exact le_trans (by linarith : (∫ y,y^2 ∂evolutionKernel β hβ ls x)≤1+(∫ y,y^2 ∂evolutionKernel β hβ ls x)) hh
  have hbh : (∫ y,y^2 ∂μ)/R^2 ≤ 1/2 := (div_le_iff₀ (sq_pos_of_pos hR)).mpr (by linarith)
  have hc : 0≤(β:ℝ)/Real.cosh ((β:ℝ)*R)^2 := by positivity
  have hsmall : (β:ℝ)/(2*Real.cosh ((β:ℝ)*R)^2)≤
      (β:ℝ)/Real.cosh ((β:ℝ)*R)^2*(1-(∫ y,y^2 ∂μ)/R^2) := by
    have he : (β:ℝ)/(2*Real.cosh ((β:ℝ)*R)^2)=((β:ℝ)/Real.cosh ((β:ℝ)*R)^2)/2 := by ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hbh hc]
  exact hsmall.trans (hle.trans (evolution_terminal_curvature_le β hβ ls x))

 

def curvatureFloor (β : ℝ≥0) (X : ℝ) : ℝ :=
  (β:ℝ)/(2*Real.cosh ((β:ℝ)*Real.sqrt (2*Real.exp (2+2*(β:ℝ)^2)*(1+X^2)))^2)

lemma curvatureFloor_pos (β : ℝ≥0) (hβ : 0<β) (X : ℝ) : 0<curvatureFloor β X := by
  unfold curvatureFloor
  exact div_pos hβ (by positivity)

lemma finite_curvature_floor (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1 ≤ β) (hd : width ls ≤ 1) {x X : ℝ} (hx : x^2≤X^2) :
    curvatureFloor β X ≤ (smoothRecursion β hβ ls).d2 x := by
  apply finite_curvature_lower β hβ ls ha hd x (Real.sqrt_pos.mpr (by positivity))
  rw [Real.sq_sqrt (by positivity)]
  exact mul_le_mul_of_nonneg_left (by linarith : 1+x^2≤1+X^2) (by positivity)

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
namespace ParisiFinite

lemma finite_gradient_floor (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1 ≤ β) (hd : width ls ≤ 1)
    {x y X : ℝ} (hx : |x|≤X) (hy : |y|≤X) (hxy : x≤y) :
    curvatureFloor β X*(y-x) ≤ (smoothRecursion β hβ ls).d1 y-(smoothRecursion β hβ ls).d1 x := by
  let f := smoothRecursion β hβ ls
  let c := curvatureFloor β X
  let g := fun z => f.d1 z-c*z
  have hg (z : ℝ) : HasDerivAt g (f.d2 z-c) z := by
    convert (f.hasD2 z).sub ((hasDerivAt_id z).const_mul c) using 1 <;>
      first | rfl | (simp only [mul_one])
  have hm : MonotoneOn g (Set.Icc (-X) X) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun z hz => (hg z).continuousAt.continuousWithinAt)
    (fun z hz => (hg z).hasDerivWithinAt)
    (fun z hz => by
      have hz' : z∈Set.Icc (-X) X := Set.mem_of_mem_of_subset hz interior_subset
      have hX : 0≤X := (abs_nonneg x).trans hx
      have hsq : z^2≤X^2 := by
        have hh := mul_nonneg (sub_nonneg.mpr hz'.2) (by linarith [hz'.1] : 0≤X+z)
        nlinarith
      exact sub_nonneg.mpr (finite_curvature_floor β hβ ls ha hd hsq))
  have hh := hm (abs_le.mp hx) (abs_le.mp hy) hxy
  dsimp [g,c,f] at hh
  linarith

lemma fieldGradient_dyadic_tendsto (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => (smoothRecursion β hβ (dyadicSchedule γ false t (1-t) n)).d1 x)
      atTop (𝓝 (fieldGradient β γ t x)) := by
  obtain ⟨m,hd,_,_,hu⟩ := dyadicEvolution_terminal_gradient β hβ hγ hb t (1-t)
  have he : fieldGradient β γ t x=m x := (hd x).deriv
  rw [he]
  exact hu.tendsto_at x

 

lemma fieldGradient_floor (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t : ℝ≥0)
    {x y X : ℝ} (hx : |x|≤X) (hy : |y|≤X) (hxy : x≤y) :
    curvatureFloor β X*(y-x) ≤ fieldGradient β γ t y-fieldGradient β γ t x := by
  apply ge_of_tendsto ((fieldGradient_dyadic_tendsto β hβ hγ hb t y).sub
    (fieldGradient_dyadic_tendsto β hβ hγ hb t x))
  exact Eventually.of_forall fun n => finite_gradient_floor β hβ _
    (dyadicSchedule_coeff_bound hb false t (1-t) n)
    (by rw [dyadicSchedule_width]; exact_mod_cast (tsub_le_self : 1-t≤(1:ℝ≥0))) hx hy hxy

lemma fieldGradient_strictMono (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t : ℝ≥0) :
    StrictMono (fieldGradient β γ t) := by
  intro x y hxy
  have hh := fieldGradient_floor β hβ hγ hb t
    (show |x|≤|x|+|y| from le_add_of_nonneg_right (abs_nonneg _))
    (show |y|≤|x|+|y| from le_add_of_nonneg_left (abs_nonneg _)) hxy.le
  have hp := mul_pos (curvatureFloor_pos β hβ (|x|+|y|)) (sub_pos.mpr hxy)
  linarith

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
namespace ParisiFinite

lemma integrable_smooth_d1_sq (f : SmoothField) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun y => f.d1 y^2) μ := by
  apply (integrable_const ((f.bound1:ℝ)^2)).mono' (by have hh:=f.continuousD1; fun_prop)
  exact ae_of_all _ (sq_bound f.normD1)

lemma smooth_integral_sq_sub (f : SmoothField) (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    (∫ y,(f.d1 y-c)^2 ∂μ)=(∫ y,f.d1 y^2 ∂μ)-2*c*(∫ y,f.d1 y ∂μ)+c^2 := by
  have he : (fun y => (f.d1 y-c)^2)=(fun y => f.d1 y^2-2*c*f.d1 y+c^2) := by
    funext y; ring
  have hs : Integrable (fun y => f.d1 y^2-2*c*f.d1 y) μ :=
    (integrable_smooth_d1_sq f μ).sub ((integrable_smooth_d1 f μ).const_mul (2*c))
  rw [he,integral_add hs (integrable_const (c^2)),
    integral_sub (integrable_smooth_d1_sq f μ) ((integrable_smooth_d1 f μ).const_mul (2*c)),
    integral_const_mul,integral_const,probReal_univ,one_smul]

lemma integrable_smooth_d1_sq_sub (f : SmoothField) (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ) :
    Integrable (fun y => (f.d1 y-c)^2) μ := by
  convert ((integrable_smooth_d1_sq f μ).sub ((integrable_smooth_d1 f μ).const_mul (2*c))).add
    (integrable_const (c^2)) using 1
  first | rfl | (ext y; simp only [Pi.add_apply,Pi.sub_apply]; ring)

 
lemma transition_gradient_variance (f : SmoothField) (a s x : ℝ) :
    (∫ y,(f.d1 y-(f.transform a s).d1 x)^2 ∂transitionMeasure f a s x)=
      (∫ y,f.d1 y^2 ∂transitionMeasure f a s x)-((f.transform a s).d1 x)^2 := by
  rw [smooth_integral_sq_sub,transition_magnetization]
  ring

 

lemma transition_gradient_variance_le {β : ℝ≥0} {f : SmoothField}
    (hf : HasParisiCurvature β f) {a : ℝ} (ha : 0≤a) (hab : a≤β) (s x : ℝ) :
    (∫ y,(f.d1 y-(f.transform a s).d1 x)^2 ∂transitionMeasure f a s x) ≤
      (β:ℝ)^2*(s^2+a*(β:ℝ)*s^4) := by
  have hmin : (∫ y,(f.d1 y-(f.transform a s).d1 x)^2 ∂transitionMeasure f a s x) ≤
      (∫ y,(f.d1 y-f.d1 x)^2 ∂transitionMeasure f a s x) := by
    rw [transition_gradient_variance,smooth_integral_sq_sub,transition_magnetization]
    nlinarith [sq_nonneg (f.d1 x-(f.transform a s).d1 x)]
  have hli (y : ℝ) : (f.d1 y-f.d1 x)^2 ≤ (β:ℝ)^2*(y-x)^2 := by
    have hh := (curvature_gradient_lipschitz hf).dist_le_mul y x
    rw [Real.dist_eq,Real.dist_eq] at hh
    have hs := mul_le_mul hh hh (abs_nonneg _) (mul_nonneg β.coe_nonneg (abs_nonneg _))
    nlinarith [sq_abs (f.d1 y-f.d1 x),sq_abs (y-x)]
  have hi := integral_mono (integrable_smooth_d1_sq_sub f _ (f.d1 x))
    ((integrable_transition_increment_sq f a s x).const_mul ((β:ℝ)^2)) hli
  rw [integral_const_mul] at hi
  exact hmin.trans (hi.trans (mul_le_mul_of_nonneg_left
    (transition_increment_bounds hf ha hab s x).2.2 (sq_nonneg _)))

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
namespace ParisiFinite

lemma transition_d1_sq_le_time {β : ℝ≥0} {f : SmoothField}
    (hf : HasParisiCurvature β f) {a : ℝ} (ha : 0≤a) (hab : a≤β)
    {d : ℝ≥0} (hd : d≤1) (x : ℝ) :
    (∫ y,f.d1 y^2 ∂transitionMeasure f a (Real.sqrt d) x) ≤
    ((f.transform a (Real.sqrt d)).d1 x)^2+(β:ℝ)^2*(1+(β:ℝ)^2)*d := by
  have hv := transition_gradient_variance_le hf ha hab (Real.sqrt d) x
  rw [transition_gradient_variance,Real.sq_sqrt d.coe_nonneg] at hv
  have he : (Real.sqrt (d:ℝ))^4=(d:ℝ)^2 := by
    rw [show (Real.sqrt (d:ℝ))^4=((Real.sqrt (d:ℝ))^2)^2 by ring,Real.sq_sqrt d.coe_nonneg]
  rw [he] at hv
  have hdd : (d:ℝ)^2≤d := by have hh : (d:ℝ)≤1 := hd; nlinarith [d.coe_nonneg]
  have hfac : a*(β:ℝ)≤(β:ℝ)^2 := by nlinarith [mul_le_mul_of_nonneg_right hab β.coe_nonneg]
  have hp := mul_le_mul hfac hdd (sq_nonneg _) (sq_nonneg (β:ℝ))
  nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg (β:ℝ))]

 

lemma evolution_d1_sq_le_time (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1≤β) (hd : width ls≤1) (x : ℝ) :
    (∫ y,(terminalField β hβ).d1 y^2 ∂evolutionKernel β hβ ls x) ≤
    ((smoothRecursion β hβ ls).d1 x)^2+(β:ℝ)^2*(1+(β:ℝ)^2)*width ls := by
  induction ls generalizing x with
  | nil => simp [evolutionKernel,Kernel.id_apply,smoothRecursion,width]
  | cons l ls ih =>
    have hw : width (l::ls)=(l.2:ℝ)+width ls := by simp [width]
    have hat : ∀ k∈ls,k.1≤β := fun k hk => ha k (List.mem_cons_of_mem _ hk)
    have hdt : width ls≤1 := by rw [hw] at hd; linarith [l.2.coe_nonneg]
    have hdl : l.2≤1 := by rw [hw] at hd; exact_mod_cast (by linarith [schedule_width_nonneg ls] : (l.2:ℝ)≤1)
    let f := smoothRecursion β hβ ls
    let K := transitionKernel f l.1 (Real.sqrt l.2)
    let C : ℝ := (β:ℝ)^2*(1+(β:ℝ)^2)
    have hi : Integrable (fun y => (terminalField β hβ).d1 y^2)
        ((evolutionKernel β hβ ls ∘ₖ K) x) := integrable_smooth_d1_sq _ _
    have hib : Integrable (fun y => f.d1 y^2+C*width ls) (K x) :=
      (integrable_smooth_d1_sq f _).add (integrable_const _)
    change (∫ y,(terminalField β hβ).d1 y^2 ∂(evolutionKernel β hβ ls ∘ₖ K) x)≤_
    rw [Kernel.integral_comp hi]
    have hh := integral_mono hi.integral_comp hib (fun y => ih hat hdt y)
    rw [integral_add (integrable_smooth_d1_sq f _) (integrable_const _),integral_const,probReal_univ,one_smul] at hh
    have hs := transition_d1_sq_le_time (smoothRecursion_hasParisiCurvature β hβ ls hat)
      l.1.coe_nonneg (by exact_mod_cast ha l (List.mem_cons_self)) hdl x
    rw [←transitionKernel_apply] at hs
    change (∫ y,f.d1 y^2 ∂K x)≤((smoothRecursion β hβ (l::ls)).d1 x)^2+C*l.2 at hs
    rw [hw]
    change _≤_+C*((l.2:ℝ)+width ls)
    linarith

lemma evolution_gradient_variance_le (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1≤β) (hd : width ls≤1) (x : ℝ) :
    (∫ y,((terminalField β hβ).d1 y-(smoothRecursion β hβ ls).d1 x)^2
      ∂evolutionKernel β hβ ls x) ≤ (β:ℝ)^2*(1+(β:ℝ)^2)*width ls := by
  rw [smooth_integral_sq_sub,evolution_magnetization]
  have hh := evolution_d1_sq_le_time β hβ ls ha hd x
  nlinarith

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
namespace ParisiFinite

lemma terminal_gradient_scaled_deriv (β : ℝ≥0) (hβ : 0<β) (z : ℝ) :
    HasDerivAt (fun s : ℝ => (terminalField β hβ).d1 (s*z)) ((β:ℝ)*z) 0 := by
  have hh := ((terminalField β hβ).hasD2 (0*z)).comp 0 ((hasDerivAt_id 0).mul_const z)
  convert hh using 1 <;> first | rfl | (simp [terminalField])

lemma terminal_gradient_ratio_tendsto (β : ℝ≥0) (hβ : 0<β) (z : ℝ) :
    Tendsto (fun s : ℝ => (terminalField β hβ).d1 (s*z)/s) (𝓝[>] 0) (𝓝 ((β:ℝ)*z)) := by
  have ht := (terminal_gradient_scaled_deriv β hβ z).tendsto_slope_zero_right
  simpa only [zero_add,zero_mul,terminalField,Real.tanh_zero,mul_zero,sub_zero,smul_eq_mul,
    div_eq_mul_inv,mul_comm] using ht

lemma terminal_gradient_ratio_bound (β : ℝ≥0) (hβ : 0<β) {s : ℝ} (hs : s≠0) (z : ℝ) :
    |(terminalField β hβ).d1 (s*z)/s| ≤ (β:ℝ)*|z| := by
  have hh := (curvature_gradient_lipschitz (terminal_hasParisiCurvature β hβ)).norm_sub_le (s*z) 0
  simp only [terminalField,mul_zero,Real.tanh_zero,sub_zero,Real.norm_eq_abs,abs_mul] at hh
  rw [abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hs)).mpr
  change |Real.tanh ((β:ℝ)*(s*z))|≤_
  nlinarith

 

lemma terminal_magnetization_ratio_second_moment (β : ℝ≥0) (hβ : 0<β) :
    Tendsto (fun s : ℝ => ∫ z,((terminalField β hβ).d1 (s*z)/s)^2 ∂gaussianReal 0 1)
      (𝓝[>] 0) (𝓝 ((β:ℝ)^2)) := by
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := gaussianReal 0 1) (F := fun s z : ℝ => ((terminalField β hβ).d1 (s*z)/s)^2)
    (f := fun z : ℝ => ((β:ℝ)*z)^2) (fun z : ℝ => (β:ℝ)^2*z^2)
    (Eventually.of_forall fun s => (((terminalField β hβ).continuousD1.comp
      (continuous_const.mul continuous_id)).div_const s |>.pow 2).aestronglyMeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with s (hs : 0<s)
      exact ae_of_all _ fun z => by
        have hh := terminal_gradient_ratio_bound β hβ hs.ne' z
        have hsq := mul_le_mul hh hh (abs_nonneg _) (by positivity : 0≤(β:ℝ)*|z|)
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_abs ((terminalField β hβ).d1 (s*z)/s),sq_abs z])
    (((memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq).const_mul ((β:ℝ)^2))
    (ae_of_all _ fun z => (terminal_gradient_ratio_tendsto β hβ z).pow 2)
  have he : (∫ z : ℝ,((β:ℝ)*z)^2 ∂gaussianReal 0 1)=(β:ℝ)^2 := by
    simp only [mul_pow,integral_const_mul,GaussianConcentration.standard_second_moment,mul_one]
  rw [he] at ht
  exact ht

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
namespace ParisiFinite

def replicaTrial (β : ℝ≥0) (s : ℝ) : ℝ :=
  step 0 s (terminal β) 0+(β:ℝ)*(1-s^2)^2/4

lemma terminal_curvature_identity (β : ℝ≥0) (hβ : 0<β) (x : ℝ) :
    (terminalField β hβ).d2 x=(β:ℝ)*(1-(terminalField β hβ).d1 x^2) := by
  change (β:ℝ)/Real.cosh ((β:ℝ)*x)^2=(β:ℝ)*(1-Real.tanh ((β:ℝ)*x)^2)
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc := (Real.cosh_pos ((β:ℝ)*x)).ne'
  have hh := Real.cosh_sq_sub_sinh_sq ((β:ℝ)*x)
  field_simp
  have hmul := congrArg (fun t : ℝ => (β:ℝ)*t) hh
  nlinarith [hmul]

lemma replicaTrial_hasDerivAt (β : ℝ≥0) (hβ : 0<β) (s : ℝ) :
    HasDerivAt (replicaTrial β)
      ((β:ℝ)*s*(s^2-(∫ z,(terminalField β hβ).d1 (s*z)^2 ∂gaussianReal 0 1))) s := by
  have hd := hasDerivAt_step_scale (terminalField β hβ) 0 s 0
  have hI : Integrable (fun z : ℝ => (terminalField β hβ).d1 (s*z)^2) (gaussianReal 0 1) := by
    apply (integrable_const (1:ℝ)).mono'
      (((terminalField β hβ).continuousD1.comp (continuous_const.mul continuous_id)).pow 2).aestronglyMeasurable
    exact ae_of_all _ fun z => by simpa only [terminalField,NNReal.coe_one,one_pow,Real.norm_eq_abs,Pi.pow_apply,Function.comp_apply,Pi.mul_apply,id_eq] using
      (sq_bound (terminalField β hβ).normD1 (s*z))
  simp only [zero_mul,add_zero,tiltedMean_zero,zero_add] at hd
  have he : (∫ z,(terminalField β hβ).d2 (s*z) ∂gaussianReal 0 1)=
      (β:ℝ)*(1-(∫ z,(terminalField β hβ).d1 (s*z)^2 ∂gaussianReal 0 1)) := by
    simp_rw [terminal_curvature_identity]
    rw [integral_const_mul,integral_sub (integrable_const (1:ℝ)) hI,
      integral_const,probReal_univ,one_smul]
  rw [he] at hd
  have hp := ((((hasDerivAt_id s).pow 2).const_sub 1).pow 2).const_mul (β:ℝ) |>.div_const 4
  convert hd.add hp using 1 <;> first | rfl | (dsimp; ring)

lemma replicaTrial_zero (β : ℝ≥0) : replicaTrial β 0=Real.log 2/(β:ℝ)+(β:ℝ)/4 := by
  simp [replicaTrial,terminal]

lemma exists_replicaTrial_decrease (β : ℝ≥0) (hb : (1:ℝ)<β) :
    ∃ s : ℝ,0<s ∧ s<1 ∧ replicaTrial β s<replicaTrial β 0 := by
  have hβ : 0<β := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ)<1) hb)
  have hβ2 : (1:ℝ)<(β:ℝ)^2 := by nlinarith
  have ht := terminal_magnetization_ratio_second_moment β hβ
  have hev := ht.eventually (Ioi_mem_nhds hβ2)
  obtain ⟨u,hu,hprop⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
  change 0<u at hu
  let d := min u 1 / 2
  have hd : 0<d := by dsimp [d]; exact div_pos (lt_min hu (by norm_num)) (by norm_num)
  have hdu : d<u := by dsimp [d]; have hh := min_le_left u 1; linarith
  have hd1 : d<1 := by dsimp [d]; have hh := min_le_right u 1; linarith
  have hanti : StrictAntiOn (replicaTrial β) (Set.Icc 0 d) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · exact (continuous_iff_continuousAt.mpr (fun s => (replicaTrial_hasDerivAt β hβ s).continuousAt)).continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      rw [(replicaTrial_hasDerivAt β hβ s).deriv]
      have hratio := hprop (show s∈Set.Ioo 0 u from ⟨hs.1,hs.2.trans hdu⟩)
      change 1<(∫ z,((terminalField β hβ).d1 (s*z)/s)^2 ∂gaussianReal 0 1) at hratio
      simp only [div_pow,integral_div] at hratio
      have hvar : s^2<(∫ z,(terminalField β hβ).d1 (s*z)^2 ∂gaussianReal 0 1) := by
        simpa only [one_mul] using (lt_div_iff₀ (sq_pos_of_pos hs.1)).mp hratio
      exact mul_neg_of_pos_of_neg (mul_pos hβ hs.1) (sub_neg.mpr hvar)
  exact ⟨d,hd,hd1,hanti ⟨le_rfl,hd.le⟩ ⟨hd.le,le_rfl⟩ hd⟩

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
namespace ParisiFinite

 

lemma pressure_lt_annealed (β : ℝ≥0) (hb : (1:ℝ)<β) :
    SKQAOA.limitingFreeEnergy β<Real.log 2/(β:ℝ)+(β:ℝ)/4 := by
  have hβ : 0<β := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ)<1) hb)
  obtain ⟨s,hs,hs1,hdec⟩ := exists_replicaTrial_decrease β hb
  let q : ℝ≥0 := ⟨s^2,sq_nonneg s⟩
  have hq : q≤1 := by change s^2≤(1:ℝ); nlinarith
  have hsqrt : Real.sqrt (q:ℝ)=s := by
    change Real.sqrt (s^2)=s
    rw [Real.sqrt_sq_eq_abs,abs_of_pos hs]
  have he : functional β (replicaSymmetricSchedule β q)=replicaTrial β s := by
    rw [replicaSymmetric_functional hβ q hq,hsqrt]
    simp only [replicaTrial,step_mean,zero_add]
    rfl
  have hbound := ParisiGuerra.limitingFreeEnergy_le_functional β hβ
    (replicaSymmetricSchedule β q) (replicaSymmetric_admissible β q hq)
  rw [he] at hbound
  simpa only [replicaTrial_zero] using hbound.trans_lt hdec

lemma dyadicEvolution_constant {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a t d : ℝ≥0) (x : ℝ) :
    dyadicEvolution (fun _ => a) t d f x=step a (Real.sqrt d) f x := by
  have hlo := le_ciSup (dyadic_low_bddAbove hf (γ:=fun _ => a) monotone_const t d x) 0
  have hup : dyadicEvolution (fun _ => a) t d f x≤
      evolve (dyadicSchedule (fun _ => a) true t d 0) f x := by
    apply ciSup_le
    intro n
    exact (dyadicSchedule_low_le_high hf monotone_const t d n x).trans
      (dyadic_high_antitone hf monotone_const t d x (Nat.zero_le n))
  change evolve (dyadicSchedule (fun _ => a) false t d 0) f x≤
    dyadicEvolution (fun _ => a) t d f x at hlo
  simpa only [dyadicSchedule,evolve] using le_antisymm hup hlo

def zeroOrderMeasure : ProbabilityMeasure OrderPoint :=
  ⟨Measure.dirac ⟨0,by norm_num⟩,inferInstance⟩

lemma zeroOrderMeasure_coefficient (β : ℝ≥0) :
    measureCoefficient zeroOrderMeasure β=fun _ => β := by
  funext s
  unfold measureCoefficient zeroOrderMeasure
  simp [Measure.real,s.coe_nonneg]

lemma zeroOrderMeasure_functional (β : ℝ≥0) (hβ : 0<β) :
    measureFunctional β zeroOrderMeasure=Real.log 2/(β:ℝ)+(β:ℝ)/4 := by
  rw [measureFunctional,zeroOrderMeasure_coefficient]
  unfold orderParameterFunctional
  rw [dyadicEvolution_constant (terminal_lipschitz (β:=(β:ℝ)) hβ) β 0 1 0]
  simp only [Real.sqrt_one,NNReal.coe_one]
  rw [step_terminal (β:=(β:ℝ)) hβ]
  have hp : coefficientPenalty (fun _ => β) 0 1=(β:ℝ)/4 := by
    unfold coefficientPenalty
    simpa using constant_coefficient_integral (β:ℝ) 0 1
  rw [hp]
  simp only [terminal,mul_zero,Real.cosh_zero,mul_one,one_pow]
  ring

 

lemma zeroOrderMeasure_not_minimizing (β : ℝ≥0) (hb : (1:ℝ)<β) :
    ¬IsMinimizingParisiMeasure β zeroOrderMeasure := by
  have hβ : 0<β := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ)<1) hb)
  obtain ⟨ρ,_,hρ⟩ := exists_minimizing_Parisi_measure hβ
  intro hmin
  have hh := hmin ρ
  rw [hρ,zeroOrderMeasure_functional β hβ] at hh
  exact (pressure_lt_annealed β hb).not_ge hh

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite

lemma shift_integrableExpSet {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (s x : ℝ) : integrableExpSet (fun z => f (x+s*z)) (gaussianReal 0 1)=Set.univ := by
  ext a
  simp only [Set.mem_univ,iff_true]
  exact integrable_exp_shift hf a x s

lemma expMass_hasDerivAt_coefficient {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a s x : ℝ) : HasDerivAt (fun r => expMass r s f x) (expMoment a s f f x) a := by
  have hm : a∈interior (integrableExpSet (fun z => f (x+s*z)) (gaussianReal 0 1)) := by
    rw [shift_integrableExpSet hf,interior_univ]
    trivial
  have hd := hasDerivAt_mgf hm
  change HasDerivAt (fun r => expMass r s f x)
    (∫ z,f (x+s*z)*Real.exp (a*f (x+s*z)) ∂gaussianReal 0 1) a at hd
  simpa only [expMoment,mul_comm] using hd

 

lemma step_hasDerivAt_coefficient {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {a : ℝ} (ha : a≠0) (s x : ℝ) :
    HasDerivAt (fun r => step r s f x) ((tiltedMean a s f f x-step a s f x)/a) a := by
  have hd := ((expMass_hasDerivAt_coefficient hf a s x).log (expMass_pos hf a s x).ne').div
    (hasDerivAt_id a) ha
  have heq : (fun r => step r s f x)=ᶠ[𝓝 a] fun r => Real.log (expMass r s f x)/r := by
    filter_upwards [eventually_ne_nhds ha] with r hr
    simp only [step,logMean,hr,↓reduceIte,expMass]
  rw [heq.hasDerivAt_iff]
  convert! hd using 1
  unfold tiltedMean step logMean
  rw [ite_eq_right ha]
  change (expMoment a s f f x / expMass a s f x-Real.log (expMass a s f x)/a)/a=_
  simp only [id_eq,mul_one]
  field_simp

lemma coefficient_cgf_second_variance {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a s x : ℝ) :
    iteratedDeriv 2 (fun r => Real.log (expMass r s f x)) a=
      tiltedMean a s f (fun y => f y^2) x-(tiltedMean a s f f x)^2 := by
  have hm : a∈interior (integrableExpSet (fun z => f (x+s*z)) (gaussianReal 0 1)) := by
    rw [shift_integrableExpSet hf,interior_univ]
    trivial
  have hh := iteratedDeriv_two_cgf hm
  rw [deriv_cgf hm] at hh
  change iteratedDeriv 2 (fun r => Real.log (expMass r s f x)) a=
    (∫ z,f (x+s*z)^2*Real.exp (a*f (x+s*z)) ∂gaussianReal 0 1)/expMass a s f x-
      ((∫ z,f (x+s*z)*Real.exp (a*f (x+s*z)) ∂gaussianReal 0 1)/expMass a s f x)^2 at hh
  simpa only [tiltedMean,expMoment,mul_comm] using hh

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite

lemma analytic_dslope_hasDerivAt {g : ℝ → ℝ} {a : ℝ} (hg : AnalyticAt ℝ g a) :
    HasDerivAt (dslope g a) (iteratedDeriv 2 g a/2) a := by
  obtain ⟨p,hp⟩ := hg
  have hd := hp.has_fpower_series_dslope_fslope.hasDerivAt
  have he : p.fslope 1 (fun _ => 1)=iteratedDeriv 2 g a/2 := by
    change p.fslope.coeff 1=iteratedDeriv 2 g a/2
    rw [FormalMultilinearSeries.coeff_fslope]
    obtain ⟨r,hr⟩ := hp
    have hh := hr.factorial_smul (1:ℝ) 2
    rw [← iteratedDeriv_eq_iteratedFDeriv] at hh
    norm_num at hh
    change p.coeff 2=_
    linarith
  rwa [he] at hd

lemma step_eq_cgf_dslope {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (s x : ℝ) : (fun a => step a s f x)=dslope (cgf (fun z => f (x+s*z)) (gaussianReal 0 1)) 0 := by
  have hm : (0:ℝ)∈interior (integrableExpSet (fun z => f (x+s*z)) (gaussianReal 0 1)) := by
    rw [shift_integrableExpSet hf,interior_univ]
    trivial
  funext a
  by_cases ha : a=0
  · subst a
    rw [dslope_same,deriv_cgf_zero hm]
    simp [step_mean]
  · rw [dslope_of_ne _ ha]
    simp [step,logMean,ha,slope,cgf,mgf,div_eq_mul_inv,mul_comm]

 

lemma step_hasDerivAt_zero_coefficient {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (s x : ℝ) : HasDerivAt (fun a => step a s f x)
      (((∫ z,f (x+s*z)^2 ∂gaussianReal 0 1)-
        (∫ z,f (x+s*z) ∂gaussianReal 0 1)^2)/2) 0 := by
  have hm : (0:ℝ)∈interior (integrableExpSet (fun z => f (x+s*z)) (gaussianReal 0 1)) := by
    rw [shift_integrableExpSet hf,interior_univ]
    trivial
  rw [step_eq_cgf_dslope hf]
  have hd := analytic_dslope_hasDerivAt (analyticAt_cgf hm)
  have hv := coefficient_cgf_second_variance hf 0 s x
  change iteratedDeriv 2 (cgf (fun z => f (x+s*z)) (gaussianReal 0 1)) 0=_ at hv
  rw [hv] at hd
  simpa only [tiltedMean_zero] using hd

 

lemma step_analyticAt_coefficient {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a s x : ℝ) : AnalyticAt ℝ (fun r => step r s f x) a := by
  have hm : a∈interior (integrableExpSet (fun z => f (x+s*z)) (gaussianReal 0 1)) := by
    rw [shift_integrableExpSet hf,interior_univ]
    trivial
  by_cases ha : a=0
  · subst a
    rw [step_eq_cgf_dslope hf]
    obtain ⟨p,hp⟩ := analyticAt_cgf hm
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  · have hh := (analyticAt_cgf hm).div analyticAt_id ha
    apply hh.congr
    filter_upwards [eventually_ne_nhds ha] with r hr
    simp only [Pi.div_apply,id_eq,cgf,mgf,step,logMean,hr,↓reduceIte]

end ParisiFinite

end

end OAI
