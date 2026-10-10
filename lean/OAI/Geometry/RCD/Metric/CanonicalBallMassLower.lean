import OAI.Geometry.RCD.Heat.CanonicalLocalLower

namespace OAI

/-! # A fixed positive heat mass in every diffusive ball

Symmetry places the volume normalization at the fixed pole. Integration
then cancels that volume exactly, without any boundary regularity.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_ball_mass_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (z : X) (r t : ℝ), 0 < r → 0 < t → t ≤ 1 → t ≤ r^2 →
      c ≤ ∫ y in ball z r, hX.canonicalHeatKernel hn p t z y ∂hausdorff n X := by
  obtain ⟨c,hc,hbound⟩ := hX.canonicalHeatKernel_local_lower hn p 1 zero_le_one
  refine ⟨c,hc,?_⟩
  intro z r t hr ht ht1 htr
  let μ := hausdorff n X
  let V := μ.real (ball z (Real.sqrt t))
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport z _ (Real.sqrt_pos.mpr ht)).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hsub : ball z (Real.sqrt t) ⊆ ball z r := by
    apply ball_subset_ball
    nlinarith [Real.sq_sqrt ht.le,Real.sqrt_nonneg t]
  have hi := hX.canonicalHeatKernel_integrable hn p t ht z
  calc
    c = ∫ y in ball z (Real.sqrt t), c/V ∂μ := by
      simp only [integral_const,smul_eq_mul,measureReal_restrict_apply MeasurableSet.univ,
        univ_inter]
      change c = V*(c/V)
      field_simp
    _ ≤ ∫ y in ball z (Real.sqrt t), hX.canonicalHeatKernel hn p t z y ∂μ := by
      apply setIntegral_mono_on (integrableOn_const (hX.finiteOnBounded _ isBounded_ball).ne)
        hi.integrableOn measurableSet_ball
      intro y hy
      rw [hX.canonicalHeatKernel_symmetric hn p t z y]
      apply hbound t ht ht1 y z
      have hd : dist y z < Real.sqrt t := hy
      nlinarith [Real.sq_sqrt ht.le,dist_nonneg (x := y) (y := z)]
    _ ≤ ∫ y in ball z r, hX.canonicalHeatKernel hn p t z y ∂μ := by
      apply setIntegral_mono_set hi.integrableOn
        (Eventually.of_forall fun y => hX.canonicalHeatKernel_nonneg hn p t z y)
      exact Eventually.of_forall hsub

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
