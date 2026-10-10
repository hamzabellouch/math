import Mathlib
import OAI.Geometry.WeakHessian.Transport.HopfObjective
import OAI.Geometry.WeakHessian.Transport.UpperEnvelope
import OAI.Geometry.WeakHessian.Transport.BoundedMarginalSum

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
open Set MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [TopologicalSpace.SeparableSpace X] [TopologicalSpace.SeparableSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

local instance boundedPosSMulMono : PosSMulMono ℝ ((X×Y) →ᵇ ℝ) where
  smul_le_smul_of_nonneg_left scalar nonneg left right pointwise := fun point =>
    mul_le_mul_of_nonneg_left (a := scalar) (b := left point) (c := right point)
      (pointwise point) nonneg

lemma bounded_marginals_of_integral_identity (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {q : Measure (X×Y)} [IsFiniteMeasure q]
    (hq : ∀ fg, (∫ p,boundedMarginalSum fg p ∂q) = boundedMarginalIntegral μ ν fg) :
    q.map Prod.fst = μ ∧ q.map Prod.snd = ν := by
  constructor
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := q) (f := f) measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
    have H := hq (compactToBounded f,0)
    simpa only [boundedMarginalSum_apply,boundedMarginalIntegral_apply,compactToBounded_apply,
      BoundedContinuousFunction.coe_zero,Pi.zero_apply,add_zero,integral_zero] using H
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := q) (f := f) measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
    have H := hq (0,compactToBounded f)
    simpa only [boundedMarginalSum_apply,boundedMarginalIntegral_apply,compactToBounded_apply,
      BoundedContinuousFunction.coe_zero,Pi.zero_apply,zero_add,integral_zero] using H

lemma bounded_kantorovich_duality (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (cost : (X×Y) →ᵇ ℝ) :
    ∃ q : Measure (X×Y), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      ∀ ε : ℝ, 0 < ε → ∃ fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ),
        boundedMarginalSum fg ≤ cost ∧
        (∫ p,cost p ∂q) < boundedMarginalIntegral μ ν fg+ε := by
  let T := boundedMarginalSum (X := X) (Y := Y)
  let c := boundedMarginalIntegral μ ν
  let l := boundedIntegral (μ.prod ν)
  have hl : Monotone l := boundedIntegral_mono _
  have hcomp : ∀ fg,l (T fg) = c fg := integral_boundedMarginalSum μ ν
  have hmajor : ∀ f,∃ fg,f ≤ T fg := exists_boundedMarginal_majorant
  obtain ⟨g,hg,hgmarg,hgcost⟩ := exists_envelope_support T c l hl hcomp hmajor (-cost)
  obtain ⟨q,hq,hgq⟩ := exists_probability_of_positive_marginal_functional μ ν g hg hgmarg
  let := hq
  have hqsum (fg) : (∫ p,boundedMarginalSum fg p ∂q) = boundedMarginalIntegral μ ν fg :=
    (hgq (T fg)).trans (hgmarg fg)
  obtain ⟨h0,h1⟩ := bounded_marginals_of_integral_identity μ ν hqsum
  have hcq : (∫ p,cost p ∂q) = -upperEnvelope T c (-cost) := by
    have H := (hgq (-cost)).trans hgcost
    change (∫ p,-cost p ∂q) = _ at H
    rw [integral_neg] at H
    linarith
  refine ⟨q,hq,h0,h1,?_⟩
  intro ε hε
  obtain ⟨fg,hfg,hfgc⟩ := envelope_lt T c hmajor
    (x := -cost) (r := upperEnvelope T c (-cost)+ε) (by linarith)
  refine ⟨-fg,?_,?_⟩
  · change T (-fg) ≤ cost
    rw [map_neg]
    simpa only [neg_neg] using neg_le_neg hfg
  · change (∫ p,cost p ∂q) < c (-fg)+ε
    rw [hcq,map_neg]
    linarith
end WeakHessianTransport

namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in

lemma bounded_lipschitz_dual_improvement {t : ℝ} (ht : 0 < t)
    (a b : X →ᵇ ℝ) (hab : ∀ x y, a x+b y ≤ dist x y^2/(2*t)) :
    ∃ f : X → ℝ, (∃ L : ℝ≥0, LipschitzWith L f) ∧
      (∀ x, |f x| ≤ ‖a‖) ∧
      (∀ x, a x ≤ hopfLax f t x) ∧ (∀ y, f y ≤ -b y) := by
  let B := ‖a‖
  have ha : ∀ x, |a x| ≤ B := fun x => a.norm_coe_le_norm x
  have hlo : ∀ x, -B ≤ -a x := fun x => by linarith [(abs_le.mp (ha x)).2]
  have hup : ∀ x, -a x ≤ B := fun x => by linarith [(abs_le.mp (ha x)).1]
  have hBU : -B ≤ B := by dsimp [B]; linarith [norm_nonneg a]
  have hlip := hopfLax_lipschitz_radius a.continuous.neg hlo hup hBU ht
    (Real.sqrt_nonneg (2*t*(B-(-B))))
    (Real.sq_sqrt (show 0 ≤ 2*t*(B-(-B)) by positivity)).ge
  let f : X → ℝ := fun y => -hopfLax (fun x => -a x) t y
  have hfbound : ∀ y, |f y| ≤ B := by
    intro y
    have H := lower_le_hopfLax hlo ht y
    have I := (hopfLax_le_self hlo ht y).trans (hup y)
    exact abs_le.mpr ⟨by dsimp [f]; linarith, by dsimp [f]; linarith⟩
  refine ⟨f, ⟨_, hlip.neg⟩, hfbound, ?_, ?_⟩
  · intro x
    apply le_csInf ⟨hopfObjective f t x x, mem_range_self x⟩
    rintro r ⟨y,rfl⟩
    have H := hopfLax_le_objective hlo ht y x
    dsimp [hopfObjective, f] at *
    rw [dist_comm y x] at H
    linarith
  · intro y
    suffices b y ≤ hopfLax (fun x => -a x) t y by
      dsimp [f]
      linarith
    apply le_csInf ⟨hopfObjective (fun x => -a x) t y y, mem_range_self y⟩
    rintro r ⟨x,rfl⟩
    have H := hab x y
    change a x + b y ≤ dist x y^2/(2*t) at H
    dsimp [hopfObjective]
    rw [dist_comm y x]
    linarith

omit [MeasurableSpace X] [BorelSpace X] in
def truncatedQuadraticCost (n : ℕ) : (X×X) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun p => min (dist p.1 p.2^2/2) (n:ℝ))
    (by fun_prop) n (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (by positivity) (Nat.cast_nonneg n))]
      exact min_le_right _ _)

omit [ProperSpace X] [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma truncatedQuadraticCost_apply (n : ℕ) (p : X×X) :
    truncatedQuadraticCost n p = min (dist p.1 p.2^2/2) (n:ℝ) := rfl

variable [TopologicalSpace.SeparableSpace X]

lemma exists_coupling_truncatedCost_of_hopf_bound (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (B : ℝ)
    (hdual : ∀ f : X →ᵇ ℝ, (∃ L : ℝ≥0, LipschitzWith L f) →
      (∫ x,hopfLax f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B/2) (n : ℕ) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∫ p,truncatedQuadraticCost n p ∂q) ≤ B/2 := by
  obtain ⟨q,hq,h0,h1,hql⟩ := bounded_kantorovich_duality μ ν (truncatedQuadraticCost n)
  let := hq
  refine ⟨q,hq,h0,h1,?_⟩
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨⟨a,b⟩,hab,habI⟩ := hql ε hε
  have hab' (x y : X) : a x+b y ≤ dist x y^2/(2*(1:ℝ)) := by
    have H := hab (x,y)
    change a x+b y ≤ min (dist x y^2/2) (n:ℝ) at H
    simpa only [mul_one] using H.trans (min_le_left _ _)
  obtain ⟨f,⟨L,hf⟩,hB,haf,hfb⟩ := bounded_lipschitz_dual_improvement (by norm_num : (0:ℝ)<1) a b hab'
  let f' : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous ‖a‖
    (fun x => by simpa only [Real.norm_eq_abs] using hB x)
  have hd := hdual f' ⟨L,hf⟩
  have hlo (x : X) : -‖a‖ ≤ f x := (abs_le.mp (hB x)).1
  have hup (x : X) : f x ≤ ‖a‖ := (abs_le.mp (hB x)).2
  have hc : Continuous (hopfLax f 1) := hopfLax_continuous hf.continuous hlo hup
    (by linarith [norm_nonneg a]) (by norm_num)
  have hi : Integrable (hopfLax f 1) μ := Integrable.of_bound hc.aestronglyMeasurable ‖a‖
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨lower_le_hopfLax hlo (by norm_num) x,
        (hopfLax_le_self hlo (by norm_num) x).trans (hup x)⟩)
  have HA := integral_mono (a.integrable μ) hi haf
  have HB := integral_mono (f'.integrable ν) (b.integrable ν).neg hfb
  change (∫ x,f x ∂ν) ≤ ∫ x,-b x ∂ν at HB
  rw [integral_neg] at HB
  change (∫ x,hopfLax f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B/2 at hd
  change (∫ p,truncatedQuadraticCost n p ∂q) < (∫ x,a x ∂μ)+(∫ x,b x ∂ν)+ε at habI
  linarith
end WeakHessianTransport

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

end
end InlinedFile0

end OAI
