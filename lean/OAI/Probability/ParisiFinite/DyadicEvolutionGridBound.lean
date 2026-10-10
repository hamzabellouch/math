import Mathlib
import OAI.Probability.ParisiFinite.DyadicMeshTendsto

namespace OAI

/-! Dyadic Evolution Grid Bound. -/

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
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma dyadicEvolution_grid_bound {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ} (hb : ∀ t,(γ t:ℝ) ≤ β)
    (t d : ℝ≥0) (n : ℕ) (x : ℝ) :
    |evolve (dyadicSchedule γ false t d n) f x-dyadicEvolution γ t d f x| ≤
      2*gaussianSmallError β (Real.sqrt (dyadicMesh d n)) := by
  have hlow : evolve (dyadicSchedule γ false t d n) f x ≤ dyadicEvolution γ t d f x :=
    le_ciSup (dyadic_low_bddAbove hf hγ t d x) n
  have hhigh : dyadicEvolution γ t d f x ≤ evolve (dyadicSchedule γ true t d n) f x := by
    apply le_of_tendsto (dyadic_low_tendsto hf hγ t d x)
    filter_upwards [eventually_ge_atTop n] with k hk
    exact (dyadicSchedule_low_le_high hf hγ t d k x).trans (dyadic_high_antitone hf hγ t d x hk)
  have he := abs_le.mp (dyadicSchedule_grid_error hb t d n hf x)
  rw [abs_of_nonpos (sub_nonpos.mpr hlow)]
  linarith

lemma dyadic_low_tendstoUniformly {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ} (hb : ∀ t,(γ t:ℝ) ≤ β)
    (t d : ℝ≥0) : TendstoUniformly (fun n => evolve (dyadicSchedule γ false t d n) f)
      (dyadicEvolution γ t d f) atTop := by
  have he : Tendsto (fun n => 2*gaussianSmallError β (Real.sqrt (dyadicMesh d n))) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using (gaussianSmallError_dyadic_tendsto β d).const_mul 2
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq,abs_sub_comm]
  exact (dyadicEvolution_grid_bound hf hγ hb t d n x).trans_lt hn

lemma dyadicSchedule_coeff_bound {γ : ℝ≥0 → ℝ≥0} {β : ℝ≥0} (hb : ∀ t,γ t ≤ β)
    (u : Bool) (t d : ℝ≥0) (n : ℕ) : ∀ l∈dyadicSchedule γ u t d n,l.1 ≤ β := by
  induction n generalizing t d with
  | zero =>
    intro l hl
    have he : l=(γ (if u then t+d else t),d) := List.mem_singleton.mp hl
    rw [he]
    exact hb _
  | succ n ih =>
    intro l hl
    rcases List.mem_append.mp hl with h|h
    · exact ih t (d/2) l h
    · exact ih (t+d/2) (d/2) l h

 

lemma dyadicEvolution_terminal_gradient (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t d : ℝ≥0) :
    ∃ m : ℝ → ℝ,
      (∀ x,HasDerivAt (dyadicEvolution γ t d (terminal β)) (m x) x) ∧
      LipschitzWith β m ∧ (∀ x,|m x| ≤ 1) ∧
      TendstoUniformly (fun n => (smoothRecursion β hβ (dyadicSchedule γ false t d n)).d1) m atTop := by
  let F (n : ℕ) := smoothRecursion β hβ (dyadicSchedule γ false t d n)
  have hc (n : ℕ) : HasParisiCurvature β (F n) :=
    smoothRecursion_hasParisiCurvature β hβ _ (dyadicSchedule_coeff_bound hb false t d n)
  have ht : TendstoUniformly (fun n => (F n).val) (dyadicEvolution γ t d (terminal β)) atTop := by
    have hv (n : ℕ) : (F n).val=evolve (dyadicSchedule γ false t d n) (terminal β) := by
      dsimp only [F]
      rw [smoothRecursion_val,recursion_eq_evolve]
    simp_rw [hv]
    exact dyadic_low_tendstoUniformly (terminal_lipschitz hβ) hγ (fun s => by exact_mod_cast hb s) t d
  obtain ⟨m,hu,hd,hl,hn⟩ := exists_uniform_derivative_limit hc ht
  exact ⟨m,hd,hl,hn,hu⟩

def field (β : ℝ≥0) (γ : ℝ≥0 → ℝ≥0) (t : ℝ≥0) (x : ℝ) : ℝ :=
  dyadicEvolution γ t (1-t) (terminal β) x

def fieldGradient (β : ℝ≥0) (γ : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ → ℝ :=
  deriv (field β γ t)

lemma hasDerivAt_field (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t : ℝ≥0) (x : ℝ) :
    HasDerivAt (field β γ t) (fieldGradient β γ t x) x := by
  obtain ⟨m,hd,_,_,_⟩ := dyadicEvolution_terminal_gradient β hβ hγ hb t (1-t)
  have hx : HasDerivAt (field β γ t) (m x) x := hd x
  change HasDerivAt (field β γ t) (deriv (field β γ t) x) x
  rw [hx.deriv]
  exact hx

lemma fieldGradient_lipschitz (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t : ℝ≥0) :
    LipschitzWith β (fieldGradient β γ t) := by
  obtain ⟨m,hd,hl,_,_⟩ := dyadicEvolution_terminal_gradient β hβ hγ hb t (1-t)
  convert hl using 1
  funext x
  exact (hd x).deriv

lemma fieldGradient_bound (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t : ℝ≥0) (x : ℝ) :
    |fieldGradient β γ t x| ≤ 1 := by
  obtain ⟨m,hd,_,hn,_⟩ := dyadicEvolution_terminal_gradient β hβ hγ hb t (1-t)
  have hx : HasDerivAt (field β γ t) (m x) x := hd x
  change |deriv (field β γ t) x| ≤ 1
  rw [hx.deriv]
  exact hn x

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma gaussian_integral_neg {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ z,f (-z) ∂gaussianReal 0 1)=∫ z,f z ∂gaussianReal 0 1 := by
  rw [← integral_map (by fun_prop : Measurable (fun z : ℝ => -z)).aemeasurable hf.aestronglyMeasurable,
    gaussianReal_map_neg,neg_zero]

lemma step_even {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (he : ∀ x,f (-x)=f x) (a s x : ℝ) : step a s f (-x)=step a s f x := by
  have hpoint (z : ℝ) : f (-x+s*(-z))=f (x+s*z) := by
    have hh : -x+s*(-z)=-(x+s*z) := by ring
    rw [hh,he]
  have hi := gaussian_integral_neg (hf.continuous.measurable.comp (by fun_prop : Measurable (fun z : ℝ => -x+s*z)))
  have hie := gaussian_integral_neg (Real.measurable_exp.comp ((hf.continuous.measurable.comp
    (by fun_prop : Measurable (fun z : ℝ => -x+s*z))).const_mul a))
  simp only [Function.comp_apply,hpoint] at hi hie
  unfold step logMean
  split_ifs
  · exact hi.symm
  · rw [← hie]

lemma evolve_even {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (he : ∀ x,f (-x)=f x) (ls : Schedule) (x : ℝ) : evolve ls f (-x)=evolve ls f x := by
  induction ls generalizing x with
  | nil => exact he x
  | cons l ls ih =>
    exact step_even (evolve_lipschitz hf ls) ih l.1 _ x

lemma field_even (β : ℝ≥0) (hβ : 0<β) (γ : ℝ≥0 → ℝ≥0) (t : ℝ≥0) (x : ℝ) :
    field β γ t (-x)=field β γ t x := by
  unfold field dyadicEvolution
  congr 1
  funext n
  exact evolve_even (terminal_lipschitz hβ) (terminal_even β) _ x

lemma fieldGradient_odd (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t : ℝ≥0) (x : ℝ) :
    fieldGradient β γ t (-x)= -fieldGradient β γ t x := by
  have hd := (hasDerivAt_field β hβ hγ hb t (-x)).comp x (hasDerivAt_neg x)
  have he : (fun y : ℝ => field β γ t (-y))=field β γ t := funext (field_even β hβ γ t)
  change HasDerivAt (fun y : ℝ => field β γ t (-y)) (fieldGradient β γ t (-x)*(-1)) x at hd
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_field β hβ hγ hb t x)
  linarith

lemma fieldGradient_zero (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t : ℝ≥0) :
    fieldGradient β γ t 0=0 := by
  have hh := fieldGradient_odd β hβ hγ hb t 0
  rw [neg_zero] at hh
  linarith

lemma dyadicEvolution_zero_width {L : ℝ≥0} {f : ℝ → ℝ} (_hf : LipschitzWith L f)
    (γ : ℝ≥0 → ℝ≥0) (t : ℝ≥0) (x : ℝ) : dyadicEvolution γ t 0 f x=f x := by
  have hh (n : ℕ) : ∀ g : ℝ → ℝ,evolve (dyadicSchedule γ false t 0 n) g=g := by
    induction n with
    | zero => intro g; funext y; simp [dyadicSchedule,evolve]
    | succ n ih =>
      intro g
      simp only [dyadicSchedule,zero_div,add_zero,evolve_append,ih]
  unfold dyadicEvolution
  simp_rw [hh]
  simp

lemma field_terminal (β : ℝ≥0) (hβ : 0<β) (γ : ℝ≥0 → ℝ≥0) (x : ℝ) :
    field β γ 1 x=Real.log (2*Real.cosh ((β:ℝ)*x))/β := by
  unfold field
  rw [tsub_self]
  exact dyadicEvolution_zero_width (terminal_lipschitz hβ) γ 1 x

lemma fieldGradient_terminal (β : ℝ≥0) (hβ : 0<β) (γ : ℝ≥0 → ℝ≥0) (x : ℝ) :
    fieldGradient β γ 1 x=Real.tanh ((β:ℝ)*x) := by
  have he : field β γ 1=terminal β := funext (field_terminal β hβ γ)
  unfold fieldGradient
  rw [he]
  exact (hasDerivAt_terminal hβ x).deriv

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma curvature_gradient_monotone {β : ℝ≥0} {f : SmoothField} (hf : HasParisiCurvature β f) :
    Monotone f.d1 :=
  monotone_of_hasDerivAt_nonneg f.hasD2 (fun x => (hf.2 x).1)

lemma fieldGradient_monotone (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t : ℝ≥0) :
    Monotone (fieldGradient β γ t) := by
  obtain ⟨m,hd,_,_,hu⟩ := dyadicEvolution_terminal_gradient β hβ hγ hb t (1-t)
  intro x y hxy
  have hm : m x ≤ m y := le_of_tendsto_of_tendsto (hu.tendsto_at x) (hu.tendsto_at y)
    (Eventually.of_forall fun n => curvature_gradient_monotone
      (smoothRecursion_hasParisiCurvature β hβ _ (dyadicSchedule_coeff_bound hb false t (1-t) n)) hxy)
  have hx : HasDerivAt (field β γ t) (m x) x := hd x
  have hy : HasDerivAt (field β γ t) (m y) y := hd y
  change deriv (field β γ t) x ≤ deriv (field β γ t) y
  rw [hx.deriv,hy.deriv]
  exact hm

lemma curvature_hamiltonian_bounds {β : ℝ≥0} {f : SmoothField}
    (hf : HasParisiCurvature β f) {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ β) (x : ℝ) :
    0 ≤ f.d2 x+a*f.d1 x^2 ∧ f.d2 x+a*f.d1 x^2 ≤ β := by
  constructor
  · exact add_nonneg (hf.2 x).1 (mul_nonneg ha (sq_nonneg _))
  · have hh := (hf.2 x).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg (f.d1 x))]

 

lemma step_curvature_time_bound {β : ℝ≥0} {f : SmoothField}
    (hf : HasParisiCurvature β f) {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ β)
    (s : ℝ) (hs : 0 ≤ s) (x : ℝ) :
    0 ≤ step a s f.val x-f.val x ∧ step a s f.val x-f.val x ≤ (β:ℝ)*s^2/2 := by
  let F (r : ℝ) := (f.transform a r).val x
  let H (r : ℝ) := (f.transform a r).d2 x+a*((f.transform a r).d1 x)^2
  have hd (r : ℝ) : HasDerivAt F (r*H r) r := hasDerivAt_transform_scale f a r x
  have hH (r : ℝ) : 0 ≤ H r ∧ H r ≤ β :=
    curvature_hamiltonian_bounds (transform_hasParisiCurvature hf ha hab r) ha hab x
  have hF : F 0=f.val x := by
    by_cases ha0 : a=0 <;> simp [F,SmoothField.transform,step,logMean,ha0]
  have hlo : MonotoneOn F (Set.Ici 0) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun r hr => (hd r).continuousAt.continuousWithinAt)
    (fun r hr => (hd r).hasDerivWithinAt)
    (fun r hr => mul_nonneg (show 0 ≤ r from (show 0 < r by simpa using hr).le) (hH r).1)
  let G (r : ℝ) := F r-(β:ℝ)*r^2/2
  have hg (r : ℝ) : HasDerivAt G (r*H r-(β:ℝ)*r) r := by
    convert (hd r).sub ((((hasDerivAt_id r).pow 2).const_mul (β:ℝ)).div_const 2) using 1 <;>
      first | rfl | (simp only [Nat.cast_ofNat,mul_one,id_eq]; ring)
  have hhi : AntitoneOn G (Set.Ici 0) := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun r hr => (hg r).continuousAt.continuousWithinAt)
    (fun r hr => (hg r).hasDerivWithinAt)
    (fun r hr => by
      have hr' : 0 ≤ r := (show 0 < r by simpa using hr).le
      have hh := mul_le_mul_of_nonneg_left (hH r).2 hr'
      nlinarith)
  have hl := hlo (by simp) (by simpa using hs) hs
  have hh := hhi (by simp) (by simpa using hs) hs
  dsimp [G] at hh
  rw [hF] at hl hh
  change f.val x ≤ step a s f.val x at hl
  change step a s f.val x-(β:ℝ)*s^2/2 ≤ f.val x-(β:ℝ)*0^2/2 at hh
  constructor <;> nlinarith

lemma recursion_terminal_time_bound (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1 ≤ β) (x : ℝ) :
    0 ≤ recursion β ls x-terminal β x ∧ recursion β ls x-terminal β x ≤ (β:ℝ)*width ls/2 := by
  induction ls with
  | nil => simp [recursion,width]
  | cons l ls ih =>
    have ht : ∀ k∈ls,k.1 ≤ β := fun k hk => ha k (List.mem_cons_of_mem _ hk)
    have hb := step_curvature_time_bound (smoothRecursion_hasParisiCurvature β hβ ls ht)
      l.1.coe_nonneg (by exact_mod_cast ha l (List.mem_cons_self)) (Real.sqrt l.2) (Real.sqrt_nonneg _) x
    rw [smoothRecursion_val,Real.sq_sqrt l.2.coe_nonneg] at hb
    have hh := ih ht
    change 0 ≤ step l.1 (Real.sqrt l.2) (recursion β ls) x-terminal β x ∧
      step l.1 (Real.sqrt l.2) (recursion β ls) x-terminal β x ≤ (β:ℝ)*width (l::ls)/2
    have hw : width (l::ls)=(l.2:ℝ)+width ls := by simp [width]
    rw [hw]
    constructor <;> nlinarith [hb.1,hb.2,hh.1,hh.2]

lemma field_terminal_time_bound (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t : ℝ≥0) (x : ℝ) :
    0 ≤ field β γ t x-terminal β x ∧ field β γ t x-terminal β x ≤ (β:ℝ)*(1-t:ℝ≥0)/2 := by
  have ht := (dyadic_low_tendsto (terminal_lipschitz hβ) hγ t (1-t) x).sub_const (terminal β x)
  have he (n : ℕ) : 0 ≤ evolve (dyadicSchedule γ false t (1-t) n) (terminal β) x-terminal β x ∧
      evolve (dyadicSchedule γ false t (1-t) n) (terminal β) x-terminal β x ≤ (β:ℝ)*(1-t:ℝ≥0)/2 := by
    have hh := recursion_terminal_time_bound β hβ _ (dyadicSchedule_coeff_bound hb false t (1-t) n) x
    rwa [recursion_eq_evolve,dyadicSchedule_width] at hh
  exact ⟨ge_of_tendsto ht (Eventually.of_forall fun n => (he n).1),
    le_of_tendsto ht (Eventually.of_forall fun n => (he n).2)⟩

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma dyadicEvolution_stable {L K : ℝ≥0} {f g : ℝ → ℝ}
    (hf : LipschitzWith L f) (hg : LipschitzWith K g)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) (c : ℝ)
    (hfg : ∀ x,|f x-g x| ≤ c) (x : ℝ) :
    |dyadicEvolution γ t d f x-dyadicEvolution γ t d g x| ≤ c := by
  apply le_of_tendsto (((dyadic_low_tendsto hf hγ t d x).sub (dyadic_low_tendsto hg hγ t d x)).abs)
  exact Eventually.of_forall fun n => evolve_stable hf hg _ c hfg x

 

lemma dyadicEvolution_half {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ} (hb : ∀ t,(γ t:ℝ) ≤ β)
    (t d : ℝ≥0) (x : ℝ) :
    dyadicEvolution γ t d f x=
      dyadicEvolution γ t (d/2) (dyadicEvolution γ (t+d/2) (d/2) f) x := by
  let g := dyadicEvolution γ (t+d/2) (d/2) f
  have hg : LipschitzWith 1 g := dyadicEvolution_lipschitz hf hγ _ _
  have hfull := (dyadic_low_tendsto hf hγ t d x).comp (tendsto_add_atTop_nat 1)
  have hleft := dyadic_low_tendsto hg hγ t (d/2) x
  have he : Tendsto (fun n => 2*gaussianSmallError β (Real.sqrt (dyadicMesh (d/2) n))) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using (gaussianSmallError_dyadic_tendsto β (d/2)).const_mul 2
  have hbnd (n : ℕ) : |evolve (dyadicSchedule γ false t d (n+1)) f x-
      evolve (dyadicSchedule γ false t (d/2) n) g x| ≤
        2*gaussianSmallError β (Real.sqrt (dyadicMesh (d/2) n)) := by
    rw [dyadicSchedule,evolve_append]
    exact evolve_stable (evolve_lipschitz hf _) hg _ _
      (fun y => dyadicEvolution_grid_bound hf hγ hb (t+d/2) (d/2) n y) x
  have hzero : |dyadicEvolution γ t d f x-dyadicEvolution γ t (d/2) g x| ≤ 0 :=
    le_of_tendsto_of_tendsto ((hfull.sub hleft).abs) he (Eventually.of_forall hbnd)
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hzero)

lemma field_half_DPP (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β)
    {t : ℝ≥0} (ht : t ≤ 1) (x : ℝ) :
    field β γ t x=dyadicEvolution γ t ((1-t)/2) (field β γ (t+(1-t)/2)) x := by
  have he : 1-(t+(1-t)/2)=(1-t)/2 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub (by have hh : (1-t)/2 ≤ 1-t := div_le_self (show 0 ≤ 1-t from zero_le) (by norm_num); exact add_le_of_le_tsub_left_of_le ht hh),
      NNReal.coe_add,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one,NNReal.coe_sub ht]
    norm_num only [NNReal.coe_one]
    ring
  unfold field
  rw [he]
  exact dyadicEvolution_half (terminal_lipschitz hβ) hγ (fun s => by exact_mod_cast hb s) t (1-t) x

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

 

def transitionMeasure (f : SmoothField) (a s x : ℝ) : Measure ℝ :=
  Measure.map (fun z : ℝ => x+s*z) ((gaussianReal 0 1).tilted (fun z => a*f.val (x+s*z)))

instance transitionMeasure_probability (f : SmoothField) (a s x : ℝ) :
    IsProbabilityMeasure (transitionMeasure f a s x) := by
  let := isProbabilityMeasure_tilted (integrable_exp_shift f.lipschitz a x s)
  unfold transitionMeasure
  infer_instance

lemma transition_integral (f : SmoothField) (a s x : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ y,g y ∂transitionMeasure f a s x=tiltedMean a s f.val g x := by
  rw [transitionMeasure,integral_map (by fun_prop) hg.aestronglyMeasurable,integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div,tiltedMean,expMoment,expMass]

 

lemma transition_magnetization (f : SmoothField) (a s x : ℝ) :
    ∫ y,f.d1 y ∂transitionMeasure f a s x=(f.transform a s).d1 x := by
  exact transition_integral f a s x f.continuousD1.measurable

lemma gaussian_density_ibp (f : SmoothField) (a s x : ℝ) :
    (∫ z : ℝ,z*Real.exp (a*f.val (x+s*z)) ∂gaussianReal 0 1)=a*s*expMoment a s f.val f.d1 x := by
  have hd (z : ℝ) : HasDerivAt (fun y => Real.exp (a*f.val (x+s*y)))
      (a*s*(Real.exp (a*f.val (x+s*z))*f.d1 (x+s*z))) z := by
    convert (((f.hasD1 (x+s*z)).comp z (((hasDerivAt_id z).const_mul s).const_add x)).const_mul a).exp using 1 <;>
      first | rfl | (simp only [Function.comp_apply,id_eq,mul_one]; ring)
  have hz : Integrable (fun z => z*Real.exp (a*f.val (x+s*z))) (gaussianReal 0 1) := by
    simpa only [mul_one] using integrable_coord_exp_weight f.lipschitz continuous_const
      (M := 1) (g := fun _ => (1:ℝ)) (by intro; norm_num) a s x
  have hh := SKGaussian.integral_mul_eq_integral_deriv hd (integrable_exp_shift f.lipschitz a x s)
    ((integrable_exp_weight f.lipschitz f.continuousD1 f.normD1 a s x).const_mul (a*s)) hz
  rw [hh,integral_const_mul]
  rfl

lemma transition_increment_mean (f : SmoothField) (a s x : ℝ) :
    (∫ y,y-x ∂transitionMeasure f a s x)=a*s^2*(f.transform a s).d1 x := by
  rw [transition_integral f a s x (by fun_prop)]
  unfold tiltedMean expMoment
  have he (z : ℝ) : Real.exp (a*f.val (x+s*z))*((x+s*z)-x)=
      s*(z*Real.exp (a*f.val (x+s*z))) := by ring
  simp_rw [he]
  rw [integral_const_mul,gaussian_density_ibp]
  change s*(a*s*expMoment a s f.val f.d1 x)/expMass a s f.val x=
    a*s^2*(expMoment a s f.val f.d1 x/expMass a s f.val x)
  ring

lemma integrable_sq_exp_shift {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) (a s x : ℝ) :
    Integrable (fun z : ℝ => z^2*Real.exp (a*f (x+s*z))) (gaussianReal 0 1) := by
  have hc := hf.continuous
  apply ((integrable_exp_abs (|a| *L*(|s|+1)+2)).const_mul (Real.exp (|a| *|f x|))).mono' (by fun_prop)
  exact ae_of_all _ fun z => by
    simp only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)]
    have hh := mul_le_mul_of_nonneg_left (coord_exp_scale_near_le hf a x s (s := s) (by simp) z) (abs_nonneg z)
    have hh' := mul_le_mul_of_nonneg_left (abs_mul_exp_le (|a| *L*(|s|+1)+1) z) (Real.exp_pos (|a| *|f x|)).le
    have e : |a| *(L:ℝ)*(|s|+1)+1+1=|a| *L*(|s|+1)+2 := by ring
    rw [e] at hh'
    nlinarith

lemma gaussian_density_second_moment (f : SmoothField) (a s x : ℝ) :
    (∫ z : ℝ,z^2*Real.exp (a*f.val (x+s*z)) ∂gaussianReal 0 1)=
      expMass a s f.val x+a*s^2*(expMoment a s f.val f.d2 x+a*expMoment a s f.val (fun y => f.d1 y^2) x) := by
  have hd (z : ℝ) : HasDerivAt (fun y => y*Real.exp (a*f.val (x+s*y)))
      (Real.exp (a*f.val (x+s*z))+a*s*(z*(Real.exp (a*f.val (x+s*z))*f.d1 (x+s*z)))) z := by
    have hv := (((f.hasD1 (x+s*z)).comp z
      (((hasDerivAt_id z).const_mul s).const_add x)).const_mul a).exp
    convert (hasDerivAt_id z).mul hv using 1 <;>
      first | rfl | (simp only [Function.comp_apply,id_eq,mul_one,one_mul]; ring)
  have hz : Integrable (fun z => z*Real.exp (a*f.val (x+s*z))) (gaussianReal 0 1) := by
    simpa only [mul_one] using integrable_coord_exp_weight f.lipschitz continuous_const
      (M := 1) (g := fun _ => (1:ℝ)) (by intro; norm_num) a s x
  have hm := integrable_coord_exp_weight f.lipschitz f.continuousD1 f.normD1 a s x
  have hs : Integrable (fun z => z*(z*Real.exp (a*f.val (x+s*z)))) (gaussianReal 0 1) := by
    simpa only [pow_two,mul_assoc] using integrable_sq_exp_shift f.lipschitz a s x
  have hh := SKGaussian.integral_mul_eq_integral_deriv hd hz
    ((integrable_exp_shift f.lipschitz a x s).add (hm.const_mul (a*s))) hs
  have he (z : ℝ) : z*(z*Real.exp (a*f.val (x+s*z)))=z^2*Real.exp (a*f.val (x+s*z)) := by ring
  simp only [he] at hh
  rw [hh,integral_add (integrable_exp_shift f.lipschitz a x s) (hm.const_mul (a*s)),integral_const_mul,
    gaussian_tilt_ibp]
  change expMass a s f.val x+a*s*(s*_) = _
  ring

lemma transition_increment_second_moment (f : SmoothField) (a s x : ℝ) :
    (∫ y,(y-x)^2 ∂transitionMeasure f a s x)=s^2+a*s^4*
      ((f.transform a s).d2 x+a*((f.transform a s).d1 x)^2) := by
  rw [transition_integral f a s x (by fun_prop)]
  unfold tiltedMean expMoment
  have he (z : ℝ) : Real.exp (a*f.val (x+s*z))*((x+s*z)-x)^2=
      s^2*(z^2*Real.exp (a*f.val (x+s*z))) := by ring
  simp_rw [he]
  rw [integral_const_mul,gaussian_density_second_moment]
  dsimp [SmoothField.transform,tiltedMean]
  have hp := (expMass_pos f.lipschitz a s x).ne'
  field_simp
  ring

 

lemma transition_increment_bounds {β : ℝ≥0} {f : SmoothField}
    (hf : HasParisiCurvature β f) {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ β) (s x : ℝ) :
    |∫ y,y-x ∂transitionMeasure f a s x| ≤ a*s^2 ∧
    s^2 ≤ (∫ y,(y-x)^2 ∂transitionMeasure f a s x) ∧
    (∫ y,(y-x)^2 ∂transitionMeasure f a s x) ≤ s^2+a*(β:ℝ)*s^4 := by
  rw [transition_increment_mean,transition_increment_second_moment]
  have hc := transform_hasParisiCurvature hf ha hab s
  have hm := (f.transform a s).normD1 x
  rw [hc.1,NNReal.coe_one] at hm
  have hH := curvature_hamiltonian_bounds hc ha hab x
  refine ⟨?_,?_,?_⟩
  · rw [abs_mul,abs_of_nonneg (mul_nonneg ha (sq_nonneg _))]
    nlinarith [mul_le_mul_of_nonneg_left hm (mul_nonneg ha (sq_nonneg s))]
  · exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg ha (by positivity : 0 ≤ s^4)) hH.1)
  · nlinarith [mul_le_mul_of_nonneg_left hH.2 (mul_nonneg ha (by positivity : 0 ≤ s^4))]

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
namespace ParisiFinite

 
def noiseTiltKernel (f : SmoothField) (a s : ℝ) : Kernel ℝ ℝ :=
  (Kernel.const ℝ (gaussianReal 0 1)).withDensity
    (fun x z => ENNReal.ofReal (Real.exp (a*f.val (x+s*z))/expMass a s f.val x))

lemma measurable_noise_density (f : SmoothField) (a s : ℝ) :
    Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (a*f.val (p.1+s*p.2))/expMass a s f.val p.1)) := by
  have hm : Continuous (expMass a s f.val) := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_expMass f a s x).continuousAt)
  have hf := f.lipschitz.continuous
  fun_prop

lemma noiseTiltKernel_apply (f : SmoothField) (a s x : ℝ) :
    noiseTiltKernel f a s x=(gaussianReal 0 1).tilted (fun z => a*f.val (x+s*z)) := by
  rw [noiseTiltKernel,Kernel.withDensity_apply _ (measurable_noise_density f a s)]
  rfl

instance noiseTiltKernel_markov (f : SmoothField) (a s : ℝ) : IsMarkovKernel (noiseTiltKernel f a s) where
  isProbabilityMeasure x := by
    rw [noiseTiltKernel_apply]
    exact isProbabilityMeasure_tilted (integrable_exp_shift f.lipschitz a x s)

 
def transitionKernel (f : SmoothField) (a s : ℝ) : Kernel ℝ ℝ :=
  (Kernel.id ×ₖ noiseTiltKernel f a s).map (fun p : ℝ × ℝ => p.1+s*p.2)

instance transitionKernel_markov (f : SmoothField) (a s : ℝ) : IsMarkovKernel (transitionKernel f a s) := by
  unfold transitionKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

lemma transitionKernel_apply (f : SmoothField) (a s x : ℝ) :
    transitionKernel f a s x=transitionMeasure f a s x := by
  rw [transitionKernel,Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
    noiseTiltKernel_apply,Measure.dirac_prod,Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

 

def evolutionKernel (β : ℝ≥0) (hβ : 0<β) : Schedule → Kernel ℝ ℝ
  | [] => Kernel.id
  | l::ls => evolutionKernel β hβ ls ∘ₖ
      transitionKernel (smoothRecursion β hβ ls) l.1 (Real.sqrt l.2)

instance evolutionKernel_markov (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) :
    IsMarkovKernel (evolutionKernel β hβ ls) := by
  induction ls with
  | nil => dsimp [evolutionKernel]; infer_instance
  | cons l ls ih =>
    let := ih
    dsimp only [evolutionKernel]
    infer_instance

lemma integrable_smooth_d1 (f : SmoothField) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable f.d1 μ := by
  exact (integrable_const (f.bound1:ℝ)).mono' f.continuousD1.aestronglyMeasurable
    (ae_of_all _ fun x => f.normD1 x)

 

lemma evolution_magnetization (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (x : ℝ) :
    (∫ y,(terminalField β hβ).d1 y ∂evolutionKernel β hβ ls x)=
      (smoothRecursion β hβ ls).d1 x := by
  induction ls generalizing x with
  | nil => simp [evolutionKernel,smoothRecursion,Kernel.id_apply]
  | cons l ls ih =>
    rw [evolutionKernel,Kernel.integral_comp (integrable_smooth_d1 _ _)]
    simp_rw [ih]
    rw [transitionKernel_apply,transition_magnetization]
    rfl

lemma evolution_tanh (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (x : ℝ) :
    (∫ y,Real.tanh ((β:ℝ)*y) ∂evolutionKernel β hβ ls x)=
      (smoothRecursion β hβ ls).d1 x := evolution_magnetization β hβ ls x

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
namespace ParisiFinite

lemma integrable_transition_sq (f : SmoothField) (a s x : ℝ) :
    Integrable (fun y : ℝ => y^2) (transitionMeasure f a s x) := by
  unfold transitionMeasure
  rw [integrable_map_measure (by fun_prop) (by fun_prop),integrable_tilted_iff
    (integrable_exp_shift f.lipschitz a x s)]
  have h0 := integrable_exp_shift f.lipschitz a x s
  have h1 : Integrable (fun z => z*Real.exp (a*f.val (x+s*z))) (gaussianReal 0 1) := by
    simpa only [mul_one] using integrable_coord_exp_weight f.lipschitz continuous_const
      (M := 1) (g := fun _ => (1:ℝ)) (by intro; norm_num) a s x
  have h2 := integrable_sq_exp_shift f.lipschitz a s x
  convert ((h0.const_mul (x^2)).add (h1.const_mul (2*x*s))).add (h2.const_mul (s^2)) using 1
  all_goals first | rfl | (ext z; simp only [Function.comp_apply,smul_eq_mul,Pi.add_apply]; ring)

lemma integrable_transition_id (f : SmoothField) (a s x : ℝ) :
    Integrable (fun y : ℝ => y) (transitionMeasure f a s x) := by
  apply ((integrable_const (1:ℝ)).add (integrable_transition_sq f a s x)).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    simp only [Real.norm_eq_abs,Pi.add_apply]
    nlinarith [sq_nonneg (|y|-1),sq_abs y]

lemma integrable_transition_increment (f : SmoothField) (a s x : ℝ) :
    Integrable (fun y : ℝ => y-x) (transitionMeasure f a s x) :=
  (integrable_transition_id f a s x).sub (integrable_const x)

lemma integrable_transition_increment_sq (f : SmoothField) (a s x : ℝ) :
    Integrable (fun y : ℝ => (y-x)^2) (transitionMeasure f a s x) := by
  convert ((integrable_transition_sq f a s x).sub ((integrable_transition_id f a s x).const_mul (2*x))).add
    (integrable_const (x^2)) using 1
  all_goals first | rfl | (ext y; simp only [Pi.sub_apply,Pi.add_apply]; ring)

lemma transition_source_second_moment (f : SmoothField) (a s x : ℝ) :
    (∫ y,y^2 ∂transitionMeasure f a s x)=x^2+2*x*(a*s^2*(f.transform a s).d1 x)+s^2+
      a*s^4*((f.transform a s).d2 x+a*((f.transform a s).d1 x)^2) := by
  have he : (fun y : ℝ => y^2)=(fun y => x^2+2*x*(y-x)+(y-x)^2) := by funext y; ring
  rw [he]
  have hi : Integrable (fun y => x^2+2*x*(y-x)) (transitionMeasure f a s x) :=
    (integrable_const (x^2)).add ((integrable_transition_increment f a s x).const_mul (2*x))
  rw [integral_add hi (integrable_transition_increment_sq f a s x),integral_add (integrable_const (x^2))
    ((integrable_transition_increment f a s x).const_mul (2*x)),integral_const_mul,
    transition_increment_mean,transition_increment_second_moment]
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  ring

 

lemma transition_lyapunov_bound {β : ℝ≥0} {f : SmoothField}
    (hf : HasParisiCurvature β f) {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ β)
    {d : ℝ≥0} (hd : d ≤ 1) (x : ℝ) :
    (∫ y,1+y^2 ∂transitionMeasure f a (Real.sqrt d) x) ≤
      Real.exp ((2+2*(β:ℝ)^2)*d)*(1+x^2) := by
  rw [integral_add (integrable_const (1:ℝ)) (integrable_transition_sq _ _ _ _),
    integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul,transition_source_second_moment]
  have hs : Real.sqrt (d:ℝ)^2=(d:ℝ) := Real.sq_sqrt d.coe_nonneg
  have hs4 : Real.sqrt (d:ℝ)^4=(d:ℝ)^2 := by nlinarith [sq_nonneg (Real.sqrt (d:ℝ)^2-(d:ℝ))]
  rw [hs,hs4]
  have hc := transform_hasParisiCurvature hf ha hab (Real.sqrt d)
  have hm := (f.transform a (Real.sqrt d)).normD1 x
  rw [hc.1,NNReal.coe_one] at hm
  have hh := curvature_hamiltonian_bounds hc ha hab x
  have habsq : a^2≤(β:ℝ)^2 := by nlinarith [β.coe_nonneg]
  have hmul := mul_le_mul_of_nonneg_left hh.2 (mul_nonneg ha (sq_nonneg (d:ℝ)))
  have hxx : 2*x*a*(f.transform a (Real.sqrt d)).d1 x ≤ x^2+(β:ℝ)^2 := by
    have hs1 : ((f.transform a (Real.sqrt d)).d1 x)^2 ≤ 1 := by
      rw [abs_le] at hm
      nlinarith
    nlinarith [sq_nonneg (x-a*(f.transform a (Real.sqrt d)).d1 x),
      mul_le_mul_of_nonneg_left hs1 (sq_nonneg a)]
  have hc0 : 0≤2+2*(β:ℝ)^2 := by positivity
  have hd' : (d:ℝ)≤1 := hd
  have hb0 := β.coe_nonneg
  have hbase : 1+x^2+2*x*(a*(d:ℝ)*(f.transform a (Real.sqrt d)).d1 x)+(d:ℝ)+
      a*(d:ℝ)^2*((f.transform a (Real.sqrt d)).d2 x+a*((f.transform a (Real.sqrt d)).d1 x)^2) ≤
      (1+(2+2*(β:ℝ)^2)*d)*(1+x^2) := by
    have hhx := mul_le_mul_of_nonneg_left hxx d.coe_nonneg
    have had := mul_le_mul_of_nonneg_right hab (mul_nonneg (β:ℝ≥0).coe_nonneg (sq_nonneg (d:ℝ)))
    have hdd := mul_le_mul_of_nonneg_left (show (d:ℝ)^2≤d by nlinarith [d.coe_nonneg]) (sq_nonneg (β:ℝ))
    have hpos := mul_nonneg (mul_nonneg hc0 d.coe_nonneg) (sq_nonneg x)
    nlinarith [mul_nonneg (sq_nonneg (β:ℝ)) d.coe_nonneg,
      mul_nonneg d.coe_nonneg (sq_nonneg x)]
  simpa only [add_assoc] using hbase.trans (mul_le_mul_of_nonneg_right (by simpa only [add_comm] using Real.add_one_le_exp ((2+2*(β:ℝ)^2)*d)) (by positivity))

end ParisiFinite

end

end OAI
