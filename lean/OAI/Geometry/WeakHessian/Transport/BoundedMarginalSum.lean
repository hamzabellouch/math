import Mathlib
import OAI.Geometry.WeakHessian.Transport.CompactBounded

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported

namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def boundedMarginalSum : ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) →ₗ[ℝ] ((X×Y) →ᵇ ℝ) where
  toFun fg := fg.1.compContinuous ⟨Prod.fst,continuous_fst⟩ +
    fg.2.compContinuous ⟨Prod.snd,continuous_snd⟩
  map_add' a b := by ext p; change (a.1 p.1+b.1 p.1)+(a.2 p.2+b.2 p.2) = _; simp; ring
  map_smul' r a := by ext p; change r*a.1 p.1+r*a.2 p.2 = r*(a.1 p.1+a.2 p.2); ring

@[simp] lemma boundedMarginalSum_apply (fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (p : X×Y) :
    boundedMarginalSum fg p = fg.1 p.1 + fg.2 p.2 := rfl

lemma exists_boundedMarginal_majorant (f : (X×Y) →ᵇ ℝ) :
    ∃ fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ), f ≤ boundedMarginalSum fg := by
  refine ⟨(BoundedContinuousFunction.const X ‖f‖,0),fun p => ?_⟩
  change f p ≤ ‖f‖+0
  simpa only [add_zero] using (le_abs_self (f p)).trans (f.norm_coe_le_norm p)

def compactTensor (f : C_c(X,ℝ)) (g : C_c(Y,ℝ)) : C_c(X×Y,ℝ) :=
  ⟨⟨fun p => f p.1*g p.2,by fun_prop⟩, by
    apply (f.hasCompactSupport.prod g.hasCompactSupport).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ ((isClosed_tsupport f).prod (isClosed_tsupport g))
    intro p hp
    exact ⟨subset_closure (fun h => hp (by simp [h])),subset_closure (fun h => hp (by simp [h]))⟩⟩

variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

def boundedIntegral (μ : Measure X) [IsFiniteMeasure μ] : (X →ᵇ ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add (f.integrable μ) (g.integrable μ)
  map_smul' r f := integral_smul r f

lemma boundedIntegral_mono (μ : Measure X) [IsFiniteMeasure μ] :
    Monotone (boundedIntegral μ) := fun f g hfg => integral_mono (f.integrable μ) (g.integrable μ) hfg

def boundedMarginalIntegral (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) →ₗ[ℝ] ℝ :=
  (boundedIntegral μ).comp (LinearMap.fst ℝ _ _) + (boundedIntegral ν).comp (LinearMap.snd ℝ _ _)

@[simp] lemma boundedMarginalIntegral_apply (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) :
    boundedMarginalIntegral μ ν fg = (∫ x,fg.1 x ∂μ)+(∫ y,fg.2 y ∂ν) := rfl

variable [TopologicalSpace.SeparableSpace X] [TopologicalSpace.SeparableSpace Y]

lemma integral_boundedMarginalSum (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) :
    boundedIntegral (μ.prod ν) (boundedMarginalSum fg) = boundedMarginalIntegral μ ν fg := by
  change (∫ p,boundedMarginalSum fg p ∂μ.prod ν) = _
  rw [integral_prod _ ((boundedMarginalSum fg).integrable _)]
  simp only [boundedMarginalSum_apply,boundedMarginalIntegral_apply]
  have H (x : X) : (∫ y,fg.1 x+fg.2 y ∂ν) = fg.1 x+∫ y,fg.2 y ∂ν := by
    rw [integral_add (integrable_const _) (fg.2.integrable ν)]; simp
  simp_rw [H]
  rw [integral_add (fg.1.integrable μ) (integrable_const _)]
  simp

variable [ProperSpace X] [ProperSpace Y]

lemma exists_probability_of_positive_marginal_functional
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : ((X×Y) →ᵇ ℝ) →ₗ[ℝ] ℝ) (hg : Monotone g)
    (hmarg : ∀ fg, g (boundedMarginalSum fg) = boundedMarginalIntegral μ ν fg) :
    ∃ q : Measure (X×Y), IsProbabilityMeasure q ∧
      ∀ f : (X×Y) →ᵇ ℝ, (∫ p,f p ∂q) = g f := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let : Nonempty Y := nonempty_of_isProbabilityMeasure ν
  obtain ⟨q,hq,hCc,hle⟩ := exists_finite_measure_le_positive_functional g hg
  let := hq
  have hc (r : ℝ) : g (BoundedContinuousFunction.const (X×Y) r) = r := by
    have H := hmarg (BoundedContinuousFunction.const X r,0)
    have he : boundedMarginalSum (BoundedContinuousFunction.const X r,(0 : Y →ᵇ ℝ)) =
        BoundedContinuousFunction.const (X×Y) r := by ext; simp
    rw [he] at H
    simpa only [boundedMarginalIntegral_apply,BoundedContinuousFunction.const_apply,
      BoundedContinuousFunction.coe_zero,Pi.zero_apply,integral_zero,add_zero,integral_const,probReal_univ,
      one_smul] using H
  have hup : q.real univ ≤ 1 := by
    simpa [hc] using hle (BoundedContinuousFunction.const (X×Y) 1) (fun _ => zero_le_one)
  let a : X := Classical.arbitrary X
  let b : Y := Classical.arbitrary Y
  have hcut (n : ℕ) : (∫ x,ballCutoff a n x ∂μ)+(∫ y,ballCutoff b n y ∂ν)-1 ≤ q.real univ := by
    have H := hg (show boundedMarginalSum (compactToBounded (ballCutoff a n),
        compactToBounded (ballCutoff b n))-BoundedContinuousFunction.const (X×Y) 1 ≤
        compactToBounded (compactTensor (ballCutoff a n) (ballCutoff b n)) from by
      intro p
      change ballCutoff a n p.1+ballCutoff b n p.2-1 ≤ ballCutoff a n p.1*ballCutoff b n p.2
      nlinarith [mul_nonneg (sub_nonneg.mpr (ballCutoff_le_one a n p.1))
        (sub_nonneg.mpr (ballCutoff_le_one b n p.2))])
    rw [map_sub,hmarg,hc,←hCc] at H
    apply H.trans
    have HI := integral_mono (μ := q) (compactTensor (ballCutoff a n) (ballCutoff b n)).integrable
      (integrable_const (1:ℝ)) (fun p => show ballCutoff a n p.1*ballCutoff b n p.2 ≤ 1 from
        (mul_le_of_le_one_right (ballCutoff_nonneg a n p.1) (ballCutoff_le_one b n p.2)).trans
          (ballCutoff_le_one a n p.1))
    simpa using HI
  have hlimX : Tendsto (fun n => ∫ x,ballCutoff a n x ∂μ) atTop (𝓝 1) := by
    have H := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : X => (1:ℝ))
      (fun n => (ballCutoff a n).continuous.aestronglyMeasurable) (integrable_const 1)
      (fun n => ae_of_all _ fun x => by change ‖ballCutoff a n x‖ ≤ 1; rw [Real.norm_eq_abs,abs_of_nonneg (ballCutoff_nonneg a n x)]; exact ballCutoff_le_one a n x)
      (ae_of_all _ fun x => tendsto_ballCutoff a x)
    simpa using H
  have hlimY : Tendsto (fun n => ∫ y,ballCutoff b n y ∂ν) atTop (𝓝 1) := by
    have H := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ : Y => (1:ℝ))
      (fun n => (ballCutoff b n).continuous.aestronglyMeasurable) (integrable_const 1)
      (fun n => ae_of_all _ fun y => by change ‖ballCutoff b n y‖ ≤ 1; rw [Real.norm_eq_abs,abs_of_nonneg (ballCutoff_nonneg b n y)]; exact ballCutoff_le_one b n y)
      (ae_of_all _ fun y => tendsto_ballCutoff b y)
    simpa using H
  have hlo : 1 ≤ q.real univ := by simpa using le_of_tendsto' ((hlimX.add hlimY).sub_const 1) hcut
  have hprob : IsProbabilityMeasure q := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top q univ) (by simp)).mp
    simpa only [ENNReal.toReal_one,Measure.real] using le_antisymm hup hlo⟩
  let := hprob
  refine ⟨q,hprob,?_⟩
  intro f
  have H := hle (f+BoundedContinuousFunction.const (X×Y) ‖f‖) (fun p => by
    change 0 ≤ f p+‖f‖
    have := (abs_le.mp (f.norm_coe_le_norm p)).1
    linarith)
  have I := hle (-f+BoundedContinuousFunction.const (X×Y) ‖f‖) (fun p => by
    change 0 ≤ -f p+‖f‖
    have := (abs_le.mp (f.norm_coe_le_norm p)).2
    linarith)
  rw [map_add,hc] at H
  rw [map_add,map_neg,hc] at I
  change (∫ p,f p+‖f‖ ∂q) ≤ _ at H
  change (∫ p,-f p+‖f‖ ∂q) ≤ _ at I
  rw [integral_add (f.integrable q) (integrable_const _)] at H
  rw [show (∫ p,-f p+‖f‖ ∂q) = (∫ p,-f p ∂q)+(∫ _ : X×Y,‖f‖ ∂q) from
    integral_add (show Integrable (fun p => -f p) q from (f.integrable q).neg) (integrable_const _),integral_neg] at I
  simp only [integral_const,probReal_univ,one_smul] at H I
  linarith

end WeakHessianTransport

end
end InlinedFile0

end OAI
