import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergySlope
import OAI.Geometry.WeakHessian.LocalBounds.RelaxedProx
import OAI.Geometry.WeakHessian.Measure.LocalSlopeNotMem

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable {m : Measure X}

def relaxedDomain (m : Measure X) : Submodule ℝ (Lp ℝ 2 m) where
  carrier := {f | ∃ D : Lp ℝ 2 m,WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m}
  zero_mem' := ⟨0,relaxedGraph_zero⟩
  add_mem' := by
    rintro f g ⟨D,hD⟩ ⟨E,hE⟩
    exact ⟨D+E,relaxedGraph_add hD hE⟩
  smul_mem' := by
    rintro a f ⟨D,hD⟩
    exact ⟨|a| • D,relaxedGraph_hom a hD⟩

variable [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma relaxedDomain_dense [IsLocallyFiniteMeasure m] :
    (relaxedDomain m).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro H hH
  change H=0
  have hAE : (H : X → ℝ) =ᵐ[m] 0 := by
    apply WeakHessianCalculus.ae_eq_zero_of_integral_lipschitz_compact
      ((Lp.memLp H).locallyIntegrable (by norm_num))
    intro φ hc hφ
    obtain ⟨L,hL⟩ := hφ
    have hm : MemLp φ 2 m := hL.continuous.memLp_of_hasCompactSupport hc
    have hd : hm.toLp φ ∈ relaxedDomain m := by
      have he : cheegerEnergy m (hm.toLp φ : X → ℝ) < ∞ := by
        rw [cheegerEnergy_congr_ae hm.coeFn_toLp]
        exact cheegerEnergy_lipschitz_compact_lt_top hL hc
      obtain ⟨D,hD,_⟩ := exists_relaxedGradient_energy_eq he
      exact ⟨D,hD⟩
    have hz := Submodule.inner_left_of_mem_orthogonal hd hH
    rw [L2.inner_def] at hz
    convert hz using 1
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with x hx
    rw [Real.inner_apply, hx]
  apply Lp.ext
  exact hAE.trans (Lp.coeFn_zero ℝ 2 m).symm

lemma relaxedProx_tendsto [IsLocallyFiniteMeasure m] (u : Lp ℝ 2 m)
    (v D : ℕ → Lp ℝ 2 m) (τ : ℕ → ℝ) (hτ : Tendsto τ atTop (𝓝 0))
    (h : ∀ n,RelaxedProx u (τ n) (v n) (D n)) : Tendsto v atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (g := fun n => ‖u-v n‖)
  · intro n
    rw [norm_sub_rev]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hd : Dense (relaxedDomain m : Set (Lp ℝ 2 m)) := by
    rw [dense_iff_closure_eq]
    exact congrArg (fun S : Submodule ℝ (Lp ℝ 2 m) => (S : Set (Lp ℝ 2 m)))
      (relaxedDomain_dense (m := m))
  obtain ⟨q,hq,hqdist⟩ := hd.exists_dist_lt u (by linarith : 0 < ε/2)
  obtain ⟨E,hE⟩ := hq
  have ht : Tendsto (fun n => ‖u-q‖^2+(τ n)^2*‖E‖^2) atTop (𝓝 (‖u-q‖^2)) := by
    simpa using tendsto_const_nhds.add ((hτ.pow 2).mul_const (‖E‖^2))
  have hsmall : ‖u-q‖^2 < ε^2 := by
    rw [dist_eq_norm] at hqdist
    nlinarith [norm_nonneg (u-q)]
  have hev := ht.eventually_lt_const hsmall
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨N,fun n hn => ?_⟩
  have HC := (h n).comparison hE
  have HH := hN n hn
  simp only [Real.dist_eq,sub_zero,abs_norm]
  nlinarith [mul_nonneg (sq_nonneg (τ n)) (sq_nonneg ‖D n‖),norm_nonneg (u-v n)]
end WeakHessian

end

end OAI
