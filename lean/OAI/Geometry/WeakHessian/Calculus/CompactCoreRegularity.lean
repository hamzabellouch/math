import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.GlobalTestCore
import OAI.Geometry.WeakHessian.LocalBounds.FormDualRegularity
import OAI.Geometry.WeakHessian.LocalBounds.FormCorePairing
import OAI.Geometry.WeakHessian.Calculus.CompactCoreLocalization

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile160
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.compact_core_localized_sobolev {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {χ : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
    {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D) :
    Sobolev m (fun x => f x*χ x) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  obtain ⟨B,hB⟩ := hχ.2.1
  let M := boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB)
  let Q := cheeger_closedQuadraticEnergy hrcd.2
  let S (u A : Lp ℝ 2 m) := ∃ g,IsTestFunction m g ∧ g =ᵐ[m] u ∧ laplacian m g =ᵐ[m] A
  have hS : ∀ u A,S u A → Q.IsFormGenerator u A := by
    intro u A ⟨g,hg,hgu,hgA⟩
    exact hrcd.1.global_formGenerator_of_isLaplacian hfin o hrcd.2 u A
      ((laplacian_isLaplacian hg.1).congr_ae hgu hgA)
  have hd : ∀ u A,Q.IsFormGenerator u A → ∃ us As : ℕ → Lp ℝ 2 m,
      (∀ n,S (us n) (As n)) ∧ Tendsto us atTop (𝓝 u) ∧ Tendsto As atTop (𝓝 A) := by
    intro u A hgen
    obtain ⟨gs,hgs,us,As,hgu,hgA,hu,hA⟩ := hrcd.original_test_graph_approx hN hfull hfin o
      (hrcd.1.global_isLaplacian_of_formGenerator hfin o hrcd.2 u A hgen)
    exact ⟨us,As,fun n => ⟨gs n,hgs n,hgu n,hgA n⟩,hu,hA⟩
  obtain ⟨C,hC,hbound⟩ := hrcd.compact_core_localized_pairing hN hfull hfin o f hof hχ hχc hD hB
  have hb : ∀ u A,S u A → |⟪M f,A⟫_ℝ| ≤ C*(‖u‖+Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal)) := by
    intro u A ⟨g,hg,hgu,hgA⟩
    exact hbound g hg u A hgu hgA
  have he := Q.finite_energy_of_generator_pairing (cheeger_domain_dense hrcd.2) (M f) hC
    (Q.generator_pairing_bound_of_graph_approx S hS hd (M f) C hb)
  have hs := (hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp (M f))).mpr he
  exact (sobolev_congr_ae (boundedMulLp_ae _ (ae_of_all m hB) f)).mp hs
end WeakHessian

end
end InlinedFile160

end OAI
