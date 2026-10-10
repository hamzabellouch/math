import Mathlib
import OAI.Probability.SKFluctuations.GaussianRootTransversality

namespace OAI

/-! Transformed Density Shape. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

namespace GaussianResidual

theorem potential_eq (R : GaussianResidual) (x : ℝ) :
    R.potential x = Real.log (Real.sqrt (2*Real.pi*R.variance))+
      x^2/(2*R.variance)-R.residual.jet 0 x := by
  have hs : 0 < Real.sqrt (2*Real.pi*R.variance) := Real.sqrt_pos.mpr (by positivity [R.positive])
  unfold potential density
  rw [Real.log_mul (realGaussianKernel_pos R.positive x).ne' (Real.exp_ne_zero _),Real.log_exp]
  simp only [realGaussianKernel,gaussianPDFReal,Real.coe_toNNReal _ R.positive.le,sub_zero]
  rw [Real.log_mul (inv_ne_zero hs.ne') (Real.exp_ne_zero _),Real.log_inv,Real.log_exp]
  ring

theorem potential_hasDerivAt (R : GaussianResidual) (x : ℝ) :
    HasDerivAt R.potential (x/R.variance-R.residual.jet 1 x) x := by
  have hh := (((hasDerivAt_id x).pow 2 |>.div_const (2*R.variance)).const_add
    (Real.log (Real.sqrt (2*Real.pi*R.variance)))).sub (R.residual.derivative 0 x)
  have he : R.potential = fun x => Real.log (Real.sqrt (2*Real.pi*R.variance))+
      x^2/(2*R.variance)-R.residual.jet 0 x := funext R.potential_eq
  rw [he]
  convert! hh using 1
  simp only [id_eq]
  ring

theorem potential_deriv (R : GaussianResidual) :
    deriv R.potential = fun x => x/R.variance-R.residual.jet 1 x :=
  funext fun x => (R.potential_hasDerivAt x).deriv

theorem potential_second_hasDerivAt (R : GaussianResidual) (x : ℝ) :
    HasDerivAt (deriv R.potential) (1/R.variance-R.residual.jet 2 x) x := by
  rw [R.potential_deriv]
  exact ((hasDerivAt_id x).div_const R.variance).sub (R.residual.derivative 1 x)

theorem potential_second (R : GaussianResidual) :
    deriv (deriv R.potential) = fun x => 1/R.variance-R.residual.jet 2 x :=
  funext fun x => (R.potential_second_hasDerivAt x).deriv

theorem potential_third_hasDerivAt (R : GaussianResidual) (x : ℝ) :
    HasDerivAt (deriv (deriv R.potential)) (-R.residual.jet 3 x) x := by
  rw [R.potential_second]
  convert! (hasDerivAt_const x (1/R.variance)).sub (R.residual.derivative 2 x) using 1
  ring

theorem potential_third (R : GaussianResidual) :
    deriv (deriv (deriv R.potential)) = fun x => -R.residual.jet 3 x :=
  funext fun x => (R.potential_third_hasDerivAt x).deriv

theorem potential_even {R : GaussianResidual} (hR : R.residual.Cone) (x : ℝ) :
    R.potential (-x) = R.potential x := by rw [R.potential_eq,R.potential_eq,neg_sq,hR.1]

theorem potential_gradient_zero {R : GaussianResidual} (hR : R.residual.Cone) :
    deriv R.potential 0 = 0 := by
  have he : (fun x => R.residual.jet 0 (-x)) = R.residual.jet 0 := funext hR.1
  have hh := (R.residual.derivative 0 (-0)).comp 0 (hasDerivAt_neg 0)
  change HasDerivAt (fun x => R.residual.jet 0 (-x)) _ 0 at hh
  rw [he] at hh
  have hd := hh.unique (R.residual.derivative 0 0)
  simp only [neg_zero,mul_neg_one] at hd
  simp only [R.potential_deriv,zero_div]
  linarith

theorem potential_curvature_lower {R : GaussianResidual} (hR : R.residual.Cone) (x : ℝ) :
    1/R.variance ≤ deriv (deriv R.potential) x := by
  rw [R.potential_second]
  linarith [hR.2.1 x]

theorem potential_shape {R : GaussianResidual} (hR : R.residual.Cone) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ deriv R.potential x ∧ 0 < deriv (deriv R.potential) x ∧
      deriv (deriv (deriv R.potential)) x ≤ 0 := by
  have hm : Monotone (deriv R.potential) := monotone_of_deriv_nonneg
    (fun y => (R.potential_second_hasDerivAt y).differentiableAt)
    (fun y => (one_div_pos.mpr R.positive).le.trans (potential_curvature_lower hR y))
  refine ⟨?_,(one_div_pos.mpr R.positive).trans_le (potential_curvature_lower hR x),?_⟩
  · have hh := hm hx
    rw [potential_gradient_zero hR] at hh
    exact hh
  · rw [R.potential_third]
    exact neg_nonpos.mpr (hR.2.2 x hx)

end GaussianResidual
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

noncomputable def ResidualJet.constant (b : ℝ) : ResidualJet where
  jet n _ := if n=0 then b else 0
  derivative n x := by
    cases n with
    | zero => simpa using hasDerivAt_const x b
    | succ n => simpa using hasDerivAt_const x (0:ℝ)
  bounded n := ⟨0,le_rfl,by intro x; simp⟩

theorem ResidualJet.constant_cone (b : ℝ) : (ResidualJet.constant b).Cone := by
  refine ⟨fun _ => rfl,?_,?_⟩ <;> simp [ResidualJet.constant]

noncomputable def GaussianResidual.initial (s : ℝ) (hs : 0 < s) (b : ℝ) : GaussianResidual :=
  ⟨s,hs,ResidualJet.constant b⟩

theorem GaussianResidual.density_initial (s : ℝ) (hs : 0 < s) (b x : ℝ) :
    (GaussianResidual.initial s hs b).density x = Real.exp b*realGaussianKernel s x := by
  change realGaussianKernel s x*Real.exp (if (0:ℕ)=0 then b else 0) = _
  rw [ite_eq_left rfl,mul_comm]

theorem GaussianResidual.density_heat_zero (R : GaussianResidual) (x : ℝ) :
    (R.heat 0 (le_refl 0)).density x = R.density x := by
  change realGaussianKernel (R.variance+0) x *
    Real.exp ((R.residual.heat (R.variance*0/(R.variance+0)) (R.variance/(R.variance+0))).jet 0 x) = _
  rw [ResidualJet.exp_heat]
  simp only [add_zero,mul_zero,zero_div,div_self R.positive.ne',one_mul,Real.toNNReal_zero,
    gaussianReal_zero_var,integral_dirac,add_zero]
  rfl

 

inductive DensityStep where
  | heat (t : ℝ≥0)
  | atom (c : ℝ≥0) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
      (l : ℝ) (t : ℝ≥0)

noncomputable def DensityStep.apply (step : DensityStep) (R : GaussianResidual) : GaussianResidual :=
  match step with
  | .heat t => R.heat t t.coe_nonneg
  | .atom c α hα l t => R.atom c α hα l t

theorem DensityStep.cone (step : DensityStep) {R : GaussianResidual} (hR : R.residual.Cone) :
    (step.apply R).residual.Cone := by
  cases step with
  | heat t => exact GaussianResidual.cone_heat hR t.coe_nonneg
  | atom c α hα l t => exact GaussianResidual.cone_atom hR c.coe_nonneg α hα l t

noncomputable def finiteTransformedResidual (s : ℝ) (hs : 0 < s) (b : ℝ) (steps : List DensityStep) :
    GaussianResidual := steps.foldl (fun R step => step.apply R) (GaussianResidual.initial s hs b)

theorem DensityStep.fold_cone (steps : List DensityStep) {R : GaussianResidual}
    (hR : R.residual.Cone) :
    (steps.foldl (fun R step => step.apply R) R).residual.Cone := by
  induction steps generalizing R with
  | nil => exact hR
  | cons h t ih => exact ih (h.cone hR)

theorem finiteTransformedResidual_cone (s : ℝ) (hs : 0 < s) (b : ℝ) (steps : List DensityStep) :
    (finiteTransformedResidual s hs b steps).residual.Cone :=
  DensityStep.fold_cone steps (ResidualJet.constant_cone b)

 

theorem finiteTransformedDensity_shape (s : ℝ) (hs : 0 < s) (b : ℝ) (steps : List DensityStep)
    {x : ℝ} (hx : 0 ≤ x) :
    let V := (finiteTransformedResidual s hs b steps).potential
    0 ≤ deriv V x ∧ 0 < deriv (deriv V) x ∧ deriv (deriv (deriv V)) x ≤ 0 :=
  GaussianResidual.potential_shape (finiteTransformedResidual_cone s hs b steps) hx

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem exp_mul_shiftedContinuation_all {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (m : ℝ) {F : ℝ → ℝ} (x : ℝ)
    (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    Real.exp (m*shiftedContinuation ν m F x) = ∫ z, Real.exp (m*F (x+z)) ∂ν := by
  by_cases hm : m = 0
  · simp [hm]
  · exact exp_mul_shiftedContinuation hm x hi

theorem realGaussianKernel_exp_shift {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (m y : ℝ) :
    (∫ x, realGaussianKernel t (x-y)*Real.exp (m*F x)) =
      Real.exp (m*shiftedContinuation (gaussianReal 0 (Real.toNNReal t)) m F y) := by
  calc
    _ = ∫ z, realGaussianKernel t ((y+z)-y)*Real.exp (m*F (y+z)) :=
      (integral_add_left_eq_self (μ := volume)
        (fun x => realGaussianKernel t (x-y)*Real.exp (m*F x)) y).symm
    _ = ∫ z, realGaussianKernel t z*Real.exp (m*F (y+z)) := by simp only [add_sub_cancel_left]
    _ = ∫ z, Real.exp (m*F (y+z)) ∂gaussianReal 0 (Real.toNNReal t) :=
      (integral_gaussianReal_eq_integral_smul (Real.toNNReal_pos.mpr ht).ne').symm
    _ = _ := (exp_mul_shiftedContinuation_all m y
      ((exponentialIncrement_gaussianReal_zero (Real.toNNReal t)).integrable_shift hF m y)).symm

namespace GaussianResidual

noncomputable def plantedDensity (R : GaussianResidual) (F : ℝ → ℝ) (m x : ℝ) : ℝ :=
  R.density x*Real.exp (m*F x)

theorem plantedDensity_pos (R : GaussianResidual) (F : ℝ → ℝ) (m x : ℝ) :
    0 < R.plantedDensity F m x := mul_pos (R.density_pos x) (Real.exp_pos _)

theorem plantedDensity_integrable (R : GaussianResidual) {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (m : ℝ) : Integrable (R.plantedDensity F m) := R.weighted_integrable hF m

theorem plantedDensity_heat_integral (R : GaussianResidual) {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (m : ℝ) :
    (∫ x, (R.heat t ht.le).plantedDensity F m x) =
      ∫ y, R.plantedDensity (shiftedContinuation (gaussianReal 0 (Real.toNNReal t)) m F) m y := by
  have hi := R.heat_joint_integrable ht hF m
  calc
    _ = ∫ x, (∫ y, realGaussianKernel t (x-y)*R.density y)*Real.exp (m*F x) := by
      simp only [plantedDensity,R.density_heat ht]
    _ = ∫ x, ∫ y, realGaussianKernel t (x-y)*R.density y*Real.exp (m*F x) := by
      simp only [integral_mul_const]
    _ = ∫ y, ∫ x, realGaussianKernel t (x-y)*R.density y*Real.exp (m*F x) :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      have he : (fun x => realGaussianKernel t (x-y)*R.density y*Real.exp (m*F x)) =
          fun x => R.density y*(realGaussianKernel t (x-y)*Real.exp (m*F x)) := by funext x; ring
      rw [he,integral_const_mul,realGaussianKernel_exp_shift ht hF]
      rfl

 

theorem plantedDensity_continuation_integrable (R : GaussianResidual) {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (m : ℝ) :
    Integrable (R.plantedDensity (shiftedContinuation (gaussianReal 0 (Real.toNNReal t)) m F) m) := by
  have hh := (R.heat_joint_integrable ht hF m).integral_prod_right
  apply hh.congr
  filter_upwards [] with y
  have he : (fun x => realGaussianKernel t (x-y)*R.density y*Real.exp (m*F x)) =
      fun x => R.density y*(realGaussianKernel t (x-y)*Real.exp (m*F x)) := by funext x; ring
  rw [he,integral_const_mul,realGaussianKernel_exp_shift ht hF]
  rfl

 

theorem plantedDensity_atom (R : GaussianResidual) (c m : ℝ) (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (x : ℝ) :
    (R.atom c α hα l t).plantedDensity (scalarProfileJet α l t 0) (m+c) x =
      R.plantedDensity (scalarProfileJet α l t 0) m x := by
  unfold plantedDensity
  rw [R.density_atom]
  calc
    _ = R.density x*Real.exp (-c*scalarProfileJet α l t 0 x+(m+c)*scalarProfileJet α l t 0 x) := by
      rw [Real.exp_add]; ring
    _ = _ := by congr 2; ring

 

theorem plantedDensity_initial_integral {s : ℝ} (hs : 0 < s)
    {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (m : ℝ) :
    (∫ x, (GaussianResidual.initial s hs
        (-m*shiftedContinuation (gaussianReal 0 (Real.toNNReal s)) m F 0)).plantedDensity F m x) = 1 := by
  simp only [plantedDensity,density_initial]
  have he : (fun x => Real.exp (-m*shiftedContinuation (gaussianReal 0 (Real.toNNReal s)) m F 0)*
      realGaussianKernel s x*Real.exp (m*F x)) =
      fun x => Real.exp (-m*shiftedContinuation (gaussianReal 0 (Real.toNNReal s)) m F 0)*
        (realGaussianKernel s (x-0)*Real.exp (m*F x)) := by funext x; simp only [sub_zero,mul_assoc]
  rw [he,integral_const_mul,realGaussianKernel_exp_shift hs hF,← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  ring

end GaussianResidual
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem realGaussianKernel_test_shift {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (A : ℝ → ℝ) (m y : ℝ) :
    (∫ x, realGaussianKernel t (x-y)*Real.exp (m*F x)*A x) =
      Real.exp (m*shiftedContinuation (gaussianReal 0 (Real.toNNReal t)) m F y)*
        shiftedMean (gaussianReal 0 (Real.toNNReal t)) m F A y := by
  have hi := (exponentialIncrement_gaussianReal_zero (Real.toNNReal t)).integrable_shift hF m y
  have hp := partition_pos m hi
  rw [exp_mul_shiftedContinuation_all m y hi]
  unfold shiftedMean tiltedMean
  rw [mul_div_cancel₀ _ hp.ne']
  calc
    _ = ∫ z, realGaussianKernel t ((y+z)-y)*Real.exp (m*F (y+z))*A (y+z) :=
      (integral_add_left_eq_self (μ := volume)
        (fun x => realGaussianKernel t (x-y)*Real.exp (m*F x)*A x) y).symm
    _ = ∫ z, realGaussianKernel t z*(A (y+z)*Real.exp (m*F (y+z))) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [add_sub_cancel_left]
      ring
    _ = _ := (integral_gaussianReal_eq_integral_smul (Real.toNNReal_pos.mpr ht).ne').symm

namespace GaussianResidual

theorem planted_test_integrable (R : GaussianResidual) {F A : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hAc : Continuous A) (hAb : AbsBounded A) (m : ℝ) :
    Integrable (fun x => R.plantedDensity F m x*A x) := by
  obtain ⟨K,_,hK⟩ := hAb
  exact (R.plantedDensity_integrable hF m).mul_bdd hAc.aestronglyMeasurable
    (ae_of_all _ fun x => hK x)

theorem heat_joint_test_integrable (R : GaussianResidual) {t : ℝ} (ht : 0 < t)
    {F A : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (hAc : Continuous A) (hAb : AbsBounded A) (m : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      realGaussianKernel t (p.1-p.2)*R.density p.2*Real.exp (m*F p.1)*A p.1)
        (volume.prod volume) := by
  obtain ⟨K,_,hK⟩ := hAb
  exact (R.heat_joint_integrable ht hF m).mul_bdd
    (hAc.comp continuous_fst).aestronglyMeasurable (ae_of_all _ fun p => hK p.1)

 

theorem plantedDensity_heat_test (R : GaussianResidual) {t : ℝ} (ht : 0 < t)
    {F A : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (hAc : Continuous A) (hAb : AbsBounded A) (m : ℝ) :
    (∫ x, (R.heat t ht.le).plantedDensity F m x*A x) =
      ∫ y, R.plantedDensity (shiftedContinuation (gaussianReal 0 (Real.toNNReal t)) m F) m y*
        shiftedMean (gaussianReal 0 (Real.toNNReal t)) m F A y := by
  have hi := R.heat_joint_test_integrable ht hF hAc hAb m
  calc
    _ = ∫ x, (∫ y, realGaussianKernel t (x-y)*R.density y)*Real.exp (m*F x)*A x := by
      simp only [plantedDensity,R.density_heat ht]
    _ = ∫ x, ∫ y, realGaussianKernel t (x-y)*R.density y*Real.exp (m*F x)*A x := by
      simp only [integral_mul_const]
    _ = ∫ y, ∫ x, realGaussianKernel t (x-y)*R.density y*Real.exp (m*F x)*A x :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      have he : (fun x => realGaussianKernel t (x-y)*R.density y*Real.exp (m*F x)*A x) =
          fun x => R.density y*(realGaussianKernel t (x-y)*Real.exp (m*F x)*A x) := by funext x; ring
      rw [he,integral_const_mul,realGaussianKernel_test_shift ht hF]
      exact mul_assoc _ _ _ |>.symm

 
theorem plantedDensity_continuation_test_integrable (R : GaussianResidual) {t : ℝ} (ht : 0 < t)
    {F A : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (hAc : Continuous A) (hAb : AbsBounded A) (m : ℝ) :
    Integrable (fun y =>
      R.plantedDensity (shiftedContinuation (gaussianReal 0 (Real.toNNReal t)) m F) m y*
        shiftedMean (gaussianReal 0 (Real.toNNReal t)) m F A y) := by
  have hi := (R.heat_joint_test_integrable ht hF hAc hAb m).integral_prod_right
  apply hi.congr
  filter_upwards [] with y
  have he : (fun x => realGaussianKernel t (x-y)*R.density y*Real.exp (m*F x)*A x) =
      fun x => R.density y*(realGaussianKernel t (x-y)*Real.exp (m*F x)*A x) := by funext x; ring
  rw [he,integral_const_mul,realGaussianKernel_test_shift ht hF]
  exact mul_assoc _ _ _ |>.symm

theorem plantedDensity_initial_test {s : ℝ} (hs : 0 < s)
    {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (A : ℝ → ℝ) (m : ℝ) :
    (∫ x, (GaussianResidual.initial s hs
      (-m*shiftedContinuation (gaussianReal 0 (Real.toNNReal s)) m F 0)).plantedDensity F m x*A x) =
        shiftedMean (gaussianReal 0 (Real.toNNReal s)) m F A 0 := by
  simp only [plantedDensity,density_initial]
  have he : (fun x => Real.exp (-m*shiftedContinuation (gaussianReal 0 (Real.toNNReal s)) m F 0)*
      realGaussianKernel s x*Real.exp (m*F x)*A x) =
      fun x => Real.exp (-m*shiftedContinuation (gaussianReal 0 (Real.toNNReal s)) m F 0)*
        (realGaussianKernel s (x-0)*Real.exp (m*F x)*A x) := by
    funext x
    simp only [sub_zero,mul_assoc]
  rw [he,integral_const_mul,realGaussianKernel_test_shift hs hF,← mul_assoc,← Real.exp_add]
  simp only [neg_mul,neg_add_cancel,Real.exp_zero,one_mul]

end GaussianResidual
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal

 theorem scalar_restrict_lipschitz {F : (Fin 1 → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) : LipschitzWith C (fun x => F (fun _ => x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_pi_const] using hF.dist_le_mul (fun _ => x) (fun _ => y)

 theorem scalar_clockTest_shiftedMean (F A : (Fin 1 → ℝ) → ℝ) (m s x : ℝ) :
    clockTest m F A s (fun _ => x) =
      shiftedMean (gaussianReal 0 (Real.toNNReal s)) m (fun y => F (fun _ => y))
        (fun y => A (fun _ => y)) x := by
  unfold clockTest shiftedMean tiltedMean
  rw [integral_pi_one,integral_pi_one]
  rfl

 theorem scalar_clockContinuation_shifted (F : (Fin 1 → ℝ) → ℝ) (m s x : ℝ) :
    clockContinuation m F s (fun _ => x) =
      shiftedContinuation (gaussianReal 0 (Real.toNNReal s)) m (fun y => F (fun _ => y)) x := by
  unfold clockContinuation shiftedContinuation
  rw [integral_pi_one]
  rfl

noncomputable def HeatJet.plantedIncoming (J : HeatJet 0) (R : GaussianResidual) (m T : ℝ) : ℝ → ℝ :=
  R.plantedDensity (fun x => clockContinuation m J.F T (fun _ => x)) m

 theorem HeatJet.plantedIncoming_integrable (J : HeatJet 0) (R : GaussianResidual) {m : ℝ}
    (hm : 0 < m) (T : ℝ) : Integrable (J.plantedIncoming R m T) :=
  R.plantedDensity_integrable (scalar_restrict_lipschitz (J.evolve hm T).lipschitz) m

 theorem HeatJet.plantedGap_test (J : HeatJet 0) (R : GaussianResidual) {m : ℝ} (hm : 0 < m)
    {T s : ℝ} (hs : s ∈ Ioo 0 T) {A : (Fin 1 → ℝ) → ℝ} (hA : BddSmooth 0 A) :
    scalarWeightedMoment (J.plantedIncoming R m T)
      (clockTest m (clockContinuation m J.F (T-s)) A s) =
      ∫ x, (R.heat s hs.1.le).plantedDensity
        (fun y => clockContinuation m J.F (T-s) (fun _ => y)) m x*A (fun _ => x) := by
  have hc : Continuous (fun x : ℝ => A (fun _ => x)) :=
    hA.continuous.comp (continuous_pi fun _ => continuous_id)
  obtain ⟨K,hK,hb⟩ := hA.bound
  have ha : AbsBounded (fun x => A (fun _ => x)) := ⟨K,hK,fun x => hb (fun _ => x)⟩
  have hd := R.plantedDensity_heat_test hs.1 (scalar_restrict_lipschitz (J.evolve hm (T-s)).lipschitz) hc ha m
  change (∫ x, (R.heat s hs.1.le).plantedDensity
    (fun y => clockContinuation m J.F (T-s) (fun _ => y)) m x*A (fun _ => x)) = _ at hd
  rw [hd]
  unfold scalarWeightedMoment
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [HeatJet.plantedIncoming,GaussianResidual.plantedDensity]
  rw [← scalar_clockContinuation_shifted,← scalar_clockTest_shiftedMean]
  have he := clockContinuation_add J.lipschitz hm.ne' hs.1.le (sub_nonneg.mpr hs.2.le) (fun _ => x)
  rw [add_sub_cancel] at he
  change R.density x*Real.exp (m*clockContinuation m J.F T (fun _ => x)) *
    clockTest m (clockContinuation m J.F (T-s)) A s (fun _ => x) =
    R.density x*Real.exp (m*clockContinuation m (clockContinuation m J.F (T-s)) s (fun _ => x)) *
    clockTest m (clockContinuation m J.F (T-s)) A s (fun _ => x)
  rw [he]
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

 
def ScalarPrefixDensity {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (q m : ℝ) (R : GaussianResidual) : Prop :=
  ∀ (A : (Fin 1 → ℝ) → ℝ) (hA : BddSmooth 2 A),
    ((scalarTailJet hT α q).withTest A hA).nonnegativeProfileTest
      (rescaledMassProfile α hT) 0 (Real.toNNReal (T*q)) 0 =
    ∫ x, R.plantedDensity (fun y => (scalarTailJet hT α q).F (fun _ => y)) m x*A (fun _ => x)

theorem scalarPrefixDensity_initial {T q m : ℝ} (hT : 0 < T) (hq : 0 < q)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo (0:ℝ) q, α.val u=m) :
    ScalarPrefixDensity hT α q m (GaussianResidual.initial (T*q) (mul_pos hT hq)
      (-m*clockContinuation m (scalarTailJet hT α q).F (T*q) 0)) := by
  intro A hA
  have hs : 0 < T*q := mul_pos hT hq
  have hh := ((scalarTailJet hT α q).withTest A hA).nonnegativeProfileTest_constant_Ioo
    (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2) hm hm1 0
    (Real.toNNReal (T*q)) (by rwa [Real.coe_toNNReal _ hs.le]) (by
      intro u hu
      change α.val (u/T)=m
      apply hf
      simp only [zero_add,Real.coe_toNNReal _ hs.le] at hu
      exact ⟨div_pos hu.1 hT,(div_lt_iff₀ hT).mpr (by nlinarith [hu.2])⟩) 0
  rw [hh]
  change clockTest m (scalarTailJet hT α q).F A (Real.toNNReal (T*q)) 0 = _
  rw [Real.coe_toNNReal _ hs.le]
  have hd := GaussianResidual.plantedDensity_initial_test hs
    (scalar_restrict_lipschitz (scalarTailJet hT α q).lipschitz) (fun x => A (fun _ => x)) m
  rw [← scalar_clockContinuation_shifted,← scalar_clockTest_shiftedMean] at hd
  exact hd.symm

theorem scalarPrefixDensity_atom {T q m c : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) {R : GaussianResidual} (hR : ScalarPrefixDensity hT α q m R) :
    ScalarPrefixDensity hT α q (m+c)
      (R.atom c (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
        (T*q) (Real.toNNReal (T*(1-q)))) := by
  intro A hA
  rw [hR A hA]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [GaussianResidual.plantedDensity]
  rw [R.density_atom c (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
    (T*q) (Real.toNNReal (T*(1-q))) x]
  change R.density x*Real.exp (m*scalarProfileJet (rescaledMassProfile α hT)
    (T*q) (Real.toNNReal (T*(1-q))) 0 x)*A (fun _ => x) = _
  have he : (scalarTailJet hT α q).F (fun _ => x)=scalarProfileJet (rescaledMassProfile α hT)
      (T*q) (Real.toNNReal (T*(1-q))) 0 x := rfl
  rw [he]
  let U := scalarProfileJet (rescaledMassProfile α hT) (T*q) (Real.toNNReal (T*(1-q))) 0 x
  change R.density x*Real.exp (m*U)*A (fun _ => x) =
    Real.exp (-c*U)*R.density x*Real.exp ((m+c)*U)*A (fun _ => x)
  have he : Real.exp (-c*U)*Real.exp ((m+c)*U)=Real.exp (m*U) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = R.density x*(Real.exp (-c*U)*Real.exp ((m+c)*U))*A (fun _ => x) := by rw [he]
    _ = _ := by ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarPrefixDensity_heat {T p q m : ℝ} (hT : 0 < T) (hp : 0 ≤ p)
    (hpq : p < q) (hq : q ≤ 1) (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo p q, α.val u=m) {R : GaussianResidual}
    (hR : ScalarPrefixDensity hT α p m R) :
    ScalarPrefixDensity hT α q m (R.heat (T*(q-p)) (mul_nonneg hT.le (sub_nonneg.mpr hpq.le))) := by
  intro A hA
  let J := scalarTailJet hT α q
  let K := J.withTest A hA
  have hd : 0 < T*(q-p) := mul_pos hT (sub_pos.mpr hpq)
  have htp : 0 ≤ T*p := mul_nonneg hT.le hp
  have htq : 0 ≤ T*q := mul_nonneg hT.le (hp.trans hpq.le)
  have he : Real.toNNReal (T*p)+Real.toNNReal (T*(q-p))=Real.toNNReal (T*q) := by
    apply NNReal.eq
    simp only [NNReal.coe_add,Real.coe_toNNReal _ htp,Real.coe_toNNReal _ hd.le,Real.coe_toNNReal _ htq]
    ring
  have hh := K.nonnegativeProfileTest_clock_concat (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) hm hm1 0
    (Real.toNNReal (T*p)) (Real.toNNReal (T*(q-p)))
    (by rwa [Real.coe_toNNReal _ hd.le]) (by
      intro u hu
      change α.val (u/T)=m
      apply hf
      simp only [zero_add,Real.coe_toNNReal _ htp,Real.coe_toNNReal _ hd.le] at hu
      exact ⟨(lt_div_iff₀ hT).mpr (by nlinarith [hu.1]),
        (div_lt_iff₀ hT).mpr (by nlinarith [hu.2])⟩) 0
  rw [he] at hh
  change K.nonnegativeProfileTest _ _ _ _ = _
  rw [hh]
  have hF : (scalarTailJet hT α p).F=(K.evolve hm (Real.toNNReal (T*(q-p)))).F := by
    rw [scalarTailJet_plateau_evolve hT hpq hq α hm hf]
    change clockContinuation m J.F (T*(q-p))=clockContinuation m K.F (Real.toNNReal (T*(q-p)))
    rw [Real.coe_toNNReal _ hd.le]
    rfl
  let B := (K.evolve hm (Real.toNNReal (T*(q-p)))).A
  have hB : BddSmooth 2 B := clockTest_bddSmooth
    (J.regular_of_smoothG (scalarTailJet_G_smooth hT α q 2)) hA m (Real.toNNReal (T*(q-p)))
  have hrep := hR B hB
  have hj := congrFun (HeatJet.nonnegativeProfileTest_congr
    (K.evolve hm (Real.toNNReal (T*(q-p)))) ((scalarTailJet hT α p).withTest B hB)
    hF.symm rfl (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p))) 0
  rw [hj,hrep]
  have hAc : Continuous (fun x : ℝ => A (fun _ => x)) :=
    hA.continuous.comp (continuous_pi fun _ => continuous_id)
  obtain ⟨M,hM,hb⟩ := hA.bound
  have hAb : AbsBounded (fun x : ℝ => A (fun _ => x)) := ⟨M,hM,fun x => hb (fun _ => x)⟩
  have hdual := R.plantedDensity_heat_test hd (scalar_restrict_lipschitz J.lipschitz) hAc hAb m
  rw [hdual]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [GaussianResidual.plantedDensity]
  rw [← scalar_clockContinuation_shifted,← scalar_clockTest_shiftedMean]
  rw [hF]
  change R.density x*Real.exp (m*clockContinuation m K.F (Real.toNNReal (T*(q-p))) (fun _ => x))*
    clockTest m K.F K.A (Real.toNNReal (T*(q-p))) (fun _ => x) = _
  rw [Real.coe_toNNReal _ hd.le]
  rfl

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

inductive ScalarFinitePositivePrefix (α : boundedMassProfiles) : ℝ → ℝ → Prop where
  | initial {q m : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hm : 0 < m) (hm1 : m ≤ 1)
      (hf : ∀ u ∈ Ioo (0:ℝ) q, α.val u=m) : ScalarFinitePositivePrefix α q m
  | step {p q a m : ℝ} (prev : ScalarFinitePositivePrefix α p a)
      (hpq : p < q) (hq : q ≤ 1) (ham : a ≤ m) (hm1 : m ≤ 1)
      (hf : ∀ u ∈ Ioo p q, α.val u=m) : ScalarFinitePositivePrefix α q m

theorem ScalarFinitePositivePrefix.bounds {α : boundedMassProfiles} {q m : ℝ}
    (h : ScalarFinitePositivePrefix α q m) : 0 < q ∧ q ≤ 1 ∧ 0 < m ∧ m ≤ 1 := by
  induction h with
  | initial hq hq1 hm hm1 _ => exact ⟨hq,hq1,hm,hm1⟩
  | step _ hpq hq ham hm1 _ ih => exact ⟨ih.1.trans hpq,hq,ih.2.2.1.trans_le ham,hm1⟩

 

theorem ScalarFinitePositivePrefix.density {T : ℝ} (hT : 0 < T)
    {α : boundedMassProfiles} {q m : ℝ} (h : ScalarFinitePositivePrefix α q m) :
    ∃ R : GaussianResidual, R.variance=T*q ∧ R.residual.Cone ∧ ScalarPrefixDensity hT α q m R := by
  induction h with
  | @initial q m hq _ hm hm1 hf =>
    refine ⟨GaussianResidual.initial (T*q) (mul_pos hT hq)
      (-m*clockContinuation m (scalarTailJet hT α q).F (T*q) 0),rfl,?_,?_⟩
    · exact ResidualJet.constant_cone _
    · exact scalarPrefixDensity_initial hT hq α hm hm1 hf
  | @step p q a m prev hpq hq ham hm1 hf ih =>
    obtain ⟨R,hv,hcone,hR⟩ := ih
    let S := R.atom (m-a) (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
      (T*p) (Real.toNNReal (T*(1-p)))
    have hs : ScalarPrefixDensity hT α p m S := by
      have hh := scalarPrefixDensity_atom (c:=m-a) hT α hR
      rwa [add_sub_cancel] at hh
    have hsc : S.residual.Cone := GaussianResidual.cone_atom hcone (sub_nonneg.mpr ham)
      (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2) _ _
    have hd : 0 ≤ T*(q-p) := mul_nonneg hT.le (sub_nonneg.mpr hpq.le)
    refine ⟨S.heat (T*(q-p)) hd,?_,GaussianResidual.cone_heat hsc hd,?_⟩
    · change R.variance+T*(q-p)=T*q
      rw [hv]
      ring
    · exact scalarPrefixDensity_heat hT prev.bounds.1.le hpq hq α
        (prev.bounds.2.2.1.trans_le ham) hm1 hf hs

 

theorem ScalarFinitePositivePrefix.density_shape {T : ℝ} (hT : 0 < T)
    {α : boundedMassProfiles} {q m : ℝ} (h : ScalarFinitePositivePrefix α q m) :
    ∃ R : GaussianResidual, ScalarPrefixDensity hT α q m R ∧ R.variance=T*q ∧
      (∀ x, 1/(T*q) ≤ deriv (deriv R.potential) x) ∧
      (∀ x, 0 ≤ x → 0 ≤ deriv R.potential x ∧
        0 < deriv (deriv R.potential) x ∧ deriv (deriv (deriv R.potential)) x ≤ 0) := by
  obtain ⟨R,hv,hc,hr⟩ := h.density hT
  refine ⟨R,hr,hv,?_,fun _ hx => GaussianResidual.potential_shape hc hx⟩
  intro x
  rw [← hv]
  exact GaussianResidual.potential_curvature_lower hc x

end SKFluctuations.Hierarchy

end

end OAI
