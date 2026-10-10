import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.MinNatTendsto
import OAI.Geometry.WeakHessian.Sobolev.DaviesGradient

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerResolvent_davies {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) (hsmall : t*(L:ℝ)^2 < 1) :
    ‖expMulLp hV.continuous.aestronglyMeasurable hB
        (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u)‖ ≤
      ‖expMulLp hV.continuous.aestronglyMeasurable hB u‖/(1-t*(L:ℝ)^2) := by
  let Q := cheeger_closedQuadraticEnergy h
  let v := (Q.scale ht).resolvent u
  let A := t⁻¹ • (v-u)
  let T := expMulLp hV.continuous.aestronglyMeasurable hB
  have hu : Q.IsFormGenerator v A := (Q.scaled_resolvent_iff ht u v).mp rfl
  have hG := hcd.global_isLaplacian_of_formGenerator hfinite o h v A hu
  have HD := hG.davies_form hfinite (hcd.global_localGradientParallelogram hfinite o h) hV hB
  rw [← expMulLp_inner hV.continuous.aestronglyMeasurable hB v A,
    ← expMulLp_norm_sq hV.continuous.aestronglyMeasurable hB v] at HD
  change ⟪T v,T A⟫_ℝ ≤ (L:ℝ)^2*‖T v‖^2 at HD
  have he : ⟪T v,T A⟫_ℝ = t⁻¹*(‖T v‖^2-⟪T v,T u⟫_ℝ) := by
    simp only [A,map_smul,map_sub,real_inner_smul_right,inner_sub_right,real_inner_self_eq_norm_sq]
  rw [he] at HD
  have HC := real_inner_le_norm (T v) (T u)
  have HI := mul_le_mul_of_nonneg_left HD ht.le
  rw [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] at HI
  change ‖T v‖ ≤ ‖T u‖/(1-t*(L:ℝ)^2)
  rw [le_div_iff₀ (sub_pos.mpr hsmall)]
  by_cases hv : ‖T v‖ = 0
  · simp only [hv,zero_mul]; positivity
  · have hvp : 0 < ‖T v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    nlinarith


lemma CurvatureDimension.cheegerResolvent_weighted {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) (hsmall : t*(L:ℝ)^2 < 1) :
    MemLp (fun x => (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) x*
      Real.exp (V x)) 2 m := by
  apply (memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable _ (B :=
    (‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2))^2) ?_).1
  intro n
  have HD := hcd.cheegerResolvent_davies hfinite o h u ht (hV.min_const (n:ℝ))
    (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) hsmall
  have HU := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n
  have H := HD.trans (div_le_div_of_nonneg_right HU (sub_pos.mpr hsmall).le)
  exact pow_le_pow_left₀ (norm_nonneg _) H 2

lemma CurvatureDimension.cheegerResolvent_weighted_norm {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) (hsmall : t*(L:ℝ)^2 < 1) :
    ‖(hcd.cheegerResolvent_weighted hfinite o h u ht hV hU hsmall).toLp
      (fun x => (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) x*
      Real.exp (V x))‖ ≤ ‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2) := by
  have H := memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable
    (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) (B :=
    (‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2))^2) (by
      intro n
      have HD := hcd.cheegerResolvent_davies hfinite o h u ht (hV.min_const (n:ℝ))
        (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) hsmall
      have HU := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n
      exact pow_le_pow_left₀ (norm_nonneg _) (HD.trans
        (div_le_div_of_nonneg_right HU (sub_pos.mpr hsmall).le)) 2)
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) (sub_pos.mpr hsmall).le)).mp
  rw [norm_toLp_sq_eq_integral]
  exact H.2

lemma IsLaplacian.memLp_gradient_mul_exp (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A : Lp ℝ 2 m} (hu : IsLaplacian m u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m) :
    MemLp (fun x => weakGradient m u x*Real.exp (V x)) 2 m := by
  let D := hu.1.2.2.toLp (weakGradient m u)
  let U := hU.toLp (fun x => u x*Real.exp (V x))
  let W := hA.toLp (fun x => A x*Real.exp (V x))
  have HD : D =ᵐ[m] weakGradient m u := hu.1.2.2.coeFn_toLp
  have Hfat := memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable D
    (B := 2*‖U‖*‖W‖+4*(L:ℝ)^2*‖U‖^2) (by
      intro n
      let bnd : ∀ᵐ x ∂m, min (V x) (n:ℝ) ≤ (n:ℝ) := ae_of_all _ (fun x => min_le_right _ _)
      let T := expMulLp (hV.min_const (n:ℝ)).continuous.aestronglyMeasurable bnd
      have H := hu.davies_gradient hfinite hpar (hV.min_const (n:ℝ)) bnd
      have he : ‖T D‖^2 = ∫ x, (weakGradient m u x)^2*Real.exp (2*min (V x) (n:ℝ)) ∂m := by
        rw [expMulLp_norm_sq]
        exact integral_congr_ae (HD.mono (fun x hx => by dsimp only; rw [hx]))
      rw [← he,← expMulLp_inner (hV.min_const (n:ℝ)).continuous.aestronglyMeasurable bnd u A,
        ← expMulLp_norm_sq (hV.min_const (n:ℝ)).continuous.aestronglyMeasurable bnd u] at H
      have hTu : ‖T u‖ ≤ ‖U‖ := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n
      have hTa : ‖T A‖ ≤ ‖W‖ := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable A hA n
      have hc : -⟪T u,T A⟫_ℝ ≤ ‖T u‖*‖T A‖ :=
        (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
      have hp : ‖T u‖*‖T A‖ ≤ ‖U‖*‖W‖ := mul_le_mul hTu hTa (norm_nonneg _) (norm_nonneg _)
      have hsq : ‖T u‖^2 ≤ ‖U‖^2 := pow_le_pow_left₀ (norm_nonneg _) hTu 2
      have hsq' := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4*(L:ℝ)^2 by positivity)
      change ‖T D‖^2 ≤ _
      nlinarith)
  exact MemLp.ae_eq (HD.mono (fun x hx => by dsimp only; rw [hx])) Hfat.1

end WeakHessian

end

end OAI
