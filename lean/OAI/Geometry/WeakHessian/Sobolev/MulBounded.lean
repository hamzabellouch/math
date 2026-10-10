import Mathlib
import OAI.Geometry.WeakHessian.Measure.AeIntegralPositiveLipschitz

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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma LocalSobolev.mul_bounded (hfinite : FiniteOnBoundedSets m) {f η : X → ℝ}
    (hf : LocalSobolev m f) (hη : LocalSobolev m η) {A B : ℝ}
    (hA : ∀ᵐ x ∂m, |η x| ≤ A) (hB : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B) :
    LocalSobolev m (fun x => f x*η x) := by
  apply (localSobolev_iff_exists_upperGradient hfinite).mpr
  exact ⟨hf.1.mul_bounded hη.1.aestronglyMeasurable hA, _,
    (weakGradient_isMinimal hf.2).1.mul_bounded (weakGradient_isMinimal hη.2).1
      hf.1 hη.1.aemeasurable hA hB⟩

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma LocallyL2.memLp_of_zero_outside_ball {f : X → ℝ} (hf : LocallyL2 m f)
    {o : X} {R : ℝ} (hR : 0 < R) (hz : ∀ᵐ x ∂m, x ∉ Metric.ball o R → f x = 0) :
    MemLp f 2 m := by
  have H := (memLp_indicator_iff_restrict measurableSet_ball).mpr (hf o R hR)
  apply H.ae_eq
  filter_upwards [hz] with x hx
  by_cases hmem : x ∈ Metric.ball o R
  · exact indicator_of_mem hmem f
  · rw [indicator_of_notMem hmem,hx hmem]

lemma LocalSobolev.sobolev_of_zero_outside_ball {f : X → ℝ} (hf : LocalSobolev m f)
    {o : X} {R : ℝ} (hR : 0 < R) (hz : ∀ᵐ x ∂m, x ∉ Metric.ball o R → f x = 0) :
    Sobolev m f := by
  refine ⟨hf.1.memLp_of_zero_outside_ball hR hz,hf,?_⟩
  apply (weakGradient_isMinimal hf.2).1.1.memLp_of_zero_outside_ball hR
  have hc : LocalSobolev m (fun _ : X => (0 : ℝ)) :=
    ⟨fun _ _ _ => MemLp.zero, _, isMinimalLocalWeakUpperGradient_const 0⟩
  filter_upwards [weakGradient_locality hf hc measurableSet_ball.compl hz,
    weakGradient_const (m := m) 0] with x hx h0 hmem
  exact (hx hmem).trans h0

lemma LocalSobolev.sobolev_of_compactSupport [Nonempty X] {f : X → ℝ}
    (hf : LocalSobolev m f) (hc : HasCompactSupport f) : Sobolev m f := by
  let o : X := Classical.arbitrary X
  obtain ⟨R,hR,hsub⟩ := hc.isBounded.subset_ball_lt 0 o
  apply hf.sobolev_of_zero_outside_ball hR
  exact ae_of_all _ fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h))

lemma LocalSobolev.mul_lipschitz_compactSupport [Nonempty X]
    (hfinite : FiniteOnBoundedSets m) {f η : X → ℝ}
    (hf : LocalSobolev m f) {L : ℝ≥0} (hη : LipschitzWith L η) (hc : HasCompactSupport η) :
    Sobolev m (fun x => f x*η x) := by
  obtain ⟨A,hA⟩ := hc.exists_bound_of_continuous hη.continuous
  apply LocalSobolev.sobolev_of_compactSupport ?_
    (hc.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right)
  apply hf.mul_bounded hfinite (localSobolev_of_lipschitz hfinite hη)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hA x)
  filter_upwards [weakGradient_nonneg (m := m) η, weakGradient_le_lipschitz hfinite hη] with x hn hL
  rwa [abs_of_nonneg hn]

lemma weakGradient_local_pointwise_parallelogram [ProperSpace X] [Nonempty X]
    (hfinite : FiniteOnBoundedSets m)
    (hpar : ∀ u v : X → ℝ, Sobolev m u → Sobolev m v →
      (∫ x, (weakGradient m (fun y => u y+v y) x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => u y-v y) x)^2 ∂m) =
      2*(∫ x, (weakGradient m u x)^2 ∂m) + 2*(∫ x, (weakGradient m v x)^2 ∂m))
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    ∀ᵐ x ∂m, (weakGradient m (fun y => f y+g y) x)^2 +
      (weakGradient m (fun y => f y-g y) x)^2 =
      2*(weakGradient m f x)^2 + 2*(weakGradient m g x)^2 := by
  let o : X := Classical.arbitrary X
  have hloc (n : ℕ) : ∀ᵐ x ∂m, x ∈ Metric.closedBall o n →
      (weakGradient m (fun y => f y+g y) x)^2 +
        (weakGradient m (fun y => f y-g y) x)^2 =
      2*(weakGradient m f x)^2 + 2*(weakGradient m g x)^2 := by
    let η : X → ℝ := fun x => thickenedIndicator zero_lt_one (Metric.closedBall o (n:ℝ)) x
    have hη : LipschitzWith (1 : ℝ≥0) η := by
      simpa only [Real.toNNReal_one,inv_one] using
        (WeakHessianCalculus.lipschitz_thickenedIndicator (s := Metric.closedBall o (n:ℝ)) zero_lt_one)
    have hηc : HasCompactSupport η :=
      WeakHessianCalculus.compact_thickenedIndicator (isCompact_closedBall o (n:ℝ)) zero_lt_one
    have hη1 {x : X} (hx : x ∈ Metric.closedBall o (n:ℝ)) : η x = 1 := by
      simp only [η,thickenedIndicator_one zero_lt_one _ hx,NNReal.coe_one]
    have hfs := hf.mul_lipschitz_compactSupport hfinite hη hηc
    have hgs := hg.mul_lipschitz_compactSupport hfinite hη hηc
    have hplus : LocalSobolev m (fun x => f x+g x) := hf.add hfinite hg
    have hminus : LocalSobolev m (fun x => f x-g x) := by
      simpa only [neg_one_mul, sub_eq_add_neg] using hf.add hfinite (hg.const_mul (-1))
    have hl {u v : X → ℝ} (hu : LocalSobolev m u) (hv : LocalSobolev m v)
        (he : ∀ x ∈ Metric.closedBall o (n:ℝ), u x = v x) :
        ∀ᵐ x ∂m, x ∈ Metric.closedBall o (n:ℝ) → weakGradient m u x = weakGradient m v x :=
      weakGradient_locality hu hv measurableSet_closedBall (ae_of_all _ he)
    filter_upwards [weakGradient_pointwise_parallelogram hfinite hpar hfs hgs,
      hl hfs.2.1 hf (fun x hx => by simp only [hη1 hx,mul_one]),
      hl hgs.2.1 hg (fun x hx => by simp only [hη1 hx,mul_one]),
      hl (hfs.add hfinite hgs).2.1 hplus (fun x hx => by simp only [hη1 hx,mul_one]),
      hl (hfs.sub hfinite hgs).2.1 hminus (fun x hx => by simp only [hη1 hx,mul_one])]
      with x hp hfx hgx hpx hmx hx
    simpa only [hfx hx,hgx hx,hpx hx,hmx hx] using hp
  filter_upwards [ae_all_iff.mpr hloc] with x hx
  obtain ⟨n,hn⟩ := exists_nat_ge (dist x o)
  exact hx n hn
end WeakHessian

end

end OAI
