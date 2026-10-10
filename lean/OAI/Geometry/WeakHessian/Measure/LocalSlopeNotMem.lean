import Mathlib
import OAI.Geometry.WeakHessian.Calculus.CompactThickenedIndicator
import OAI.Geometry.WeakHessian.LocalBounds.Domain
import OAI.Geometry.WeakHessian.Sobolev.CheegerClosedQuadraticEnergy

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
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional

variable {X : Type*} [MetricSpace X]

lemma localSlope_eq_zero_of_notMem_tsupport {f : X → ℝ} {x : X} (hx : x ∉ tsupport f) :
    localSlope f x = 0 := by
  have hn : ∀ᶠ y in 𝓝 x, f y = 0 := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  calc
    localSlope f x = localSlope (fun _ : X => (0:ℝ)) x := by
      apply Filter.limsup_congr
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with y hy
      simp only [hy, image_eq_zero_of_notMem_tsupport hx, sub_self]
    _ = 0 := localSlope_zero x

variable [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma cheegerEnergy_lipschitz_compact_lt_top [IsLocallyFiniteMeasure m]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hc : HasCompactSupport f) :
    cheegerEnergy m f < ∞ := by
  have hm : MemLp f 2 m := hf.continuous.memLp_of_hasCompactSupport hc
  have he : (∫⁻ x, localSlope f x ^ 2 ∂m) < ∞ := by
    calc
      (∫⁻ x, localSlope f x ^ 2 ∂m) ≤ ∫⁻ x, (tsupport f).indicator (fun _ => (L:ℝ≥0∞)^2) x ∂m := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ tsupport f
        · rw [Set.indicator_of_mem hx]
          exact pow_le_pow_left' (localSlope_le_lipschitz hf x) 2
        · simp only [Set.indicator_of_notMem hx, localSlope_eq_zero_of_notMem_tsupport hx,
            zero_pow (by omega : (2:ℕ) ≠ 0), le_refl]
      _ = (L:ℝ≥0∞)^2 * m (tsupport f) := by
        rw [lintegral_indicator (isClosed_tsupport f).measurableSet, lintegral_const,
          Measure.restrict_apply_univ]
      _ < ∞ := ENNReal.mul_lt_top (by finiteness) hc.measure_lt_top
  have H := cheegerEnergy_le_liminf hm (fs := fun _ => f)
    (fun _ => ⟨⟨L,hf⟩, hm⟩) (by simp)
  rw [liminf_const] at H
  exact H.trans_lt (ENNReal.mul_lt_top (by norm_num) he)

lemma cheeger_domain_dense [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [IsLocallyFiniteMeasure m] (h : QuadraticCheegerEnergy m) :
    (cheeger_closedQuadraticEnergy h).domain.topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro H hH
  change H = 0
  have hAE : (H : X → ℝ) =ᵐ[m] 0 := by
    apply WeakHessianCalculus.ae_eq_zero_of_integral_lipschitz_compact
      ((Lp.memLp H).locallyIntegrable (by norm_num))
    intro φ hc hφ
    obtain ⟨L,hL⟩ := hφ
    have hm : MemLp φ 2 m := hL.continuous.memLp_of_hasCompactSupport hc
    have hd : hm.toLp φ ∈ (cheeger_closedQuadraticEnergy h).domain := by
      change cheegerEnergy m (hm.toLp φ : X → ℝ) < ∞
      rw [cheegerEnergy_congr_ae hm.coeFn_toLp]
      exact cheegerEnergy_lipschitz_compact_lt_top hL hc
    have hz := Submodule.inner_left_of_mem_orthogonal hd hH
    rw [L2.inner_def] at hz
    convert hz using 1
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]
  apply Lp.ext
  exact hAE.trans (Lp.coeFn_zero ℝ 2 m).symm

end WeakHessian

open Set Filter
open scoped Topology ENNReal NNReal

end
end InlinedFile0

end OAI
