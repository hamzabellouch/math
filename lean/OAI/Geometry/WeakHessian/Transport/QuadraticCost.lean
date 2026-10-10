import Mathlib
import OAI.Geometry.WeakHessian.Transport.HopfObjective
import OAI.Geometry.WeakHessian.Transport.UpperEnvelope
import OAI.Geometry.WeakHessian.Transport.CcConst

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

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
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology

namespace WeakHessianTransport
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

local instance ccPosSMulMono : PosSMulMono ℝ C_c(X×Y,ℝ) where
  smul_le_smul_of_nonneg_left r hr f g hfg := by
    intro p
    exact mul_le_mul_of_nonneg_left (hfg p) hr

lemma compact_kantorovich_duality (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (cost : C_c(X×Y,ℝ)) :
    ∃ q : Measure (X×Y), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∀ q' : Measure (X×Y), q'.map Prod.fst = μ → q'.map Prod.snd = ν →
        (∫ p, cost p ∂q) ≤ ∫ p, cost p ∂q') ∧
      ∀ ε : ℝ, 0 < ε → ∃ fg : C_c(X,ℝ) × C_c(Y,ℝ),
        marginalSum fg ≤ cost ∧
        (∫ p, cost p ∂q) < marginalIntegral μ ν fg + ε := by
  let T : (C_c(X,ℝ) × C_c(Y,ℝ)) →ₗ[ℝ] C_c(X×Y,ℝ) := marginalSum
  let c := marginalIntegral μ ν
  let l := (integralPositiveLinearMap (μ.prod ν)).toLinearMap
  have hl : Monotone l := (integralPositiveLinearMap (μ.prod ν)).monotone
  have hcomp : ∀ fg, l (T fg) = c fg := integral_marginalSum μ ν
  have hmajor : ∀ h, ∃ fg, h ≤ T fg := exists_marginal_majorant
  obtain ⟨g,hgpos,hgmarg,hgcost⟩ := exists_envelope_support T c l hl hcomp hmajor (-cost)
  obtain ⟨q,hqfinite,hq⟩ := exists_measure_of_positive_functional g hgpos
  let _ := hqfinite
  have hqsum (fg) : (∫ p, marginalSum fg p ∂q) = marginalIntegral μ ν fg :=
    (hq (T fg)).trans (hgmarg fg)
  obtain ⟨hq0,hq1⟩ := marginals_of_integral_identity μ ν hqsum
  have hcq : (∫ p, cost p ∂q) = - upperEnvelope T c (-cost) := by
    have H := (hq (-cost)).trans hgcost
    change (∫ p, -cost p ∂q) = upperEnvelope T c (-cost) at H
    rw [integral_neg] at H
    linarith
  refine ⟨q, probability_of_first_marginal hq0, hq0, hq1, ?_, ?_⟩
  · intro q' hq'0 hq'1
    let _ := probability_of_first_marginal hq'0
    let l' := (integralPositiveLinearMap q').toLinearMap
    have hl' : Monotone l' := (integralPositiveLinearMap q').monotone
    have hcomp' : ∀ fg, l' (T fg) = c fg := integral_marginalSum_of_marginals μ ν hq'0 hq'1
    have H := lower_le_envelope T c l' hl' hcomp' hmajor (-cost)
    change (∫ p, -cost p ∂q') ≤ upperEnvelope T c (-cost) at H
    rw [integral_neg] at H
    rw [hcq]
    linarith
  · intro ε hε
    obtain ⟨fg,hfg,hfgc⟩ := envelope_lt T c hmajor
      (x := -cost) (r := upperEnvelope T c (-cost)+ε) (by linarith)
    refine ⟨-fg, ?_, ?_⟩
    · change T (-fg) ≤ cost
      rw [map_neg]
      simpa only [neg_neg] using neg_le_neg hfg
    · change (∫ p, cost p ∂q) < c (-fg)+ε
      rw [hcq, map_neg]
      linarith

end WeakHessianTransport

open Set Filter
open scoped Topology ENNReal NNReal


namespace WeakHessianTransport
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

def quadraticCost (t : ℝ) : C_c(X×X,ℝ) :=
  ⟨⟨fun p => dist p.1 p.2 ^ 2 / (2*t), by fun_prop⟩,
    HasCompactSupport.of_compactSpace _⟩

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma quadraticCost_apply (t : ℝ) (p : X×X) :
    quadraticCost t p = dist p.1 p.2 ^ 2 / (2*t) := rfl

omit [MeasurableSpace X] [BorelSpace X] in

lemma lipschitz_dual_improvement {t : ℝ} (ht : 0 < t)
    (a b : C_c(X,ℝ)) (hab : marginalSum (a,b) ≤ quadraticCost t) :
    ∃ f : X → ℝ, (∃ L : ℝ≥0, LipschitzWith L f) ∧
      (∀ x, |f x| ≤ ‖a.toContinuousMap‖) ∧
      (∀ x, a x ≤ hopfLax f t x) ∧ (∀ y, f y ≤ -b y) := by
  let B := ‖a.toContinuousMap‖
  have ha : ∀ x, |a x| ≤ B := fun x => a.toContinuousMap.norm_coe_le_norm x
  have hlo : ∀ x, -B ≤ -a x := fun x => by linarith [(abs_le.mp (ha x)).2]
  have hup : ∀ x, -a x ≤ B := fun x => by linarith [(abs_le.mp (ha x)).1]
  have hBU : -B ≤ B := by dsimp [B]; linarith [norm_nonneg a.toContinuousMap]
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
    have H := hab (x,y)
    change a x + b y ≤ dist x y^2/(2*t) at H
    dsimp [hopfObjective]
    rw [dist_comm y x]
    linarith

lemma compact_hopf_duality (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {t : ℝ} (ht : 0 < t) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∀ q' : Measure (X×X), q'.map Prod.fst = μ → q'.map Prod.snd = ν →
        (∫ p, quadraticCost t p ∂q) ≤ ∫ p, quadraticCost t p ∂q') ∧
      ∀ ε : ℝ, 0 < ε → ∃ f : X → ℝ, (∃ L : ℝ≥0, LipschitzWith L f) ∧
        (∫ p, quadraticCost t p ∂q) <
          (∫ x, hopfLax f t x ∂μ) - (∫ x, f x ∂ν) + ε := by
  obtain ⟨q,hqp,hq0,hq1,hqmin,hqdual⟩ := compact_kantorovich_duality μ ν (quadraticCost t)
  refine ⟨q,hqp,hq0,hq1,hqmin,?_⟩
  intro ε hε
  obtain ⟨⟨a,b⟩,hab,hεdual⟩ := hqdual ε hε
  obtain ⟨f,⟨L,hf⟩,hfbd,haf,hfb⟩ := lipschitz_dual_improvement ht a b hab
  have hfcont := hf.continuous
  have hfint : Integrable f ν := hfcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hlo : ∀ x, -‖a.toContinuousMap‖ ≤ f x := fun x => (abs_le.mp (hfbd x)).1
  have hup : ∀ x, f x ≤ ‖a.toContinuousMap‖ := fun x => (abs_le.mp (hfbd x)).2
  have hQint : Integrable (hopfLax f t) μ :=
    (hopfLax_continuous hfcont hlo hup (by linarith [norm_nonneg a.toContinuousMap]) ht).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have H := integral_mono a.integrable hQint haf
  have I := integral_mono hfint b.integrable.neg hfb
  change (∫ x, f x ∂ν) ≤ ∫ x, -b x ∂ν at I
  rw [integral_neg] at I
  refine ⟨f, ⟨L,hf⟩, ?_⟩
  change (∫ p, quadraticCost t p ∂q) < (∫ x, a x ∂μ)+(∫ y, b y ∂ν)+ε at hεdual
  linarith

end WeakHessianTransport

open Set

end

end OAI
