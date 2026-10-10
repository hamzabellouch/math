import OAI.Geometry.IsometricImmersion.Darboux.QResidualL2

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Analytic

def QActiveComponents (w : ChainWord) (r : Fin w.arity → Fin 6) : Prop :=
  ∀ i, r i ≠ 1 ∧ (r i = 0 → w.order i = 1)

theorem q_state_factor_eq_zero_of_spatial_inactive
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (n : ℕ) (hn : 0 < n) (k : Fin 6) (hk : k = 1 ∨ (k = 0 ∧ n ≠ 1)) :
    horizontalJet (qSolutionJet z) n p k = 0 := by
  rw [coordinate_qSolutionJet_horizontal_positive hU hz hp n hn]
  rcases hk with hk | ⟨hk, hn1⟩
  · subst k
    rfl
  · subst k
    simp [hn1]

theorem qCoordinateChainProduct_eq_zero_of_inactive
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (w : ChainWord) (hpos : w.Positive) (r : Fin w.arity → Fin 6)
    (hinactive : ¬ QActiveComponents w r) :
    (∏ i, qCoordinateChainFactor z w r i p) = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hinactive
  have hbad : r i = 1 ∨ (r i = 0 ∧ w.order i ≠ 1) := by
    by_cases h1 : r i = 1
    · exact Or.inl h1
    · right
      have hh : ¬ (r i = 0 → w.order i = 1) := fun himp => hi ⟨h1, himp⟩
      by_cases hzero : r i = 0
      · exact ⟨hzero, fun horder => hh (fun _ => horder)⟩
      · exact (hh (fun heq => (hzero heq).elim)).elim
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (q_state_factor_eq_zero_of_spatial_inactive hU hz hp (w.order i) (hpos i) (r i) hbad)

theorem qCoordinateChainTerm_slice_eLpNorm_two_active
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor C : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3) (hC : 0 ≤ C)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    {w : ChainWord} (hw : w ∈ topResidualWords m)
    (hcoeff : ∀ r, QActiveComponents w r → ∀ x ∈ Icc left right,
      |qCoordinateChainCoefficient g z w r (coordinatePoint x theta)| ≤ C) :
    eLpNorm (fun x => qCoordinateChainTerm g z w (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qWordSliceBudget C lengthFloor left right H w := by
  classical
  have he : (fun x => qCoordinateChainTerm g z w (coordinatePoint x theta)) = fun x =>
      ∑ r : Fin w.arity → Fin 6, qCoordinateChainCoefficient g z w r (coordinatePoint x theta) *
        ∏ i, qCoordinateChainFactor z w r i (coordinatePoint x theta) :=
    funext (fun x => qCoordinateChainTerm_scalar_expansion g z w (coordinatePoint x theta))
  rw [he]
  apply finite_sum_eLpNorm_two (μ := volume) (U := Icc left right) Finset.univ _
    (fun _ => ‖C‖ₑ * spatialProductL2Budget lengthFloor left right H w.arity)
  · intro r _
    exact (smooth_slice_memLp_two
      (qCoordinateScalarTerm_continuousOn hg hU hz hxx w r) hseg).aestronglyMeasurable
  · intro r _
    by_cases hactive : QActiveComponents w r
    · exact (real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable hC (hcoeff r hactive)
        (smooth_slice_memLp_two
          (qCoordinateScalarTerm_continuousOn hg hU hz hxx w r) hseg).aestronglyMeasurable).trans
        (mul_le_mul' le_rfl (q_residual_product_eLpNorm_two hU hz hseg hlength hwidth hm hL2 hw r))
    · have hzero : (fun x => qCoordinateChainCoefficient g z w r (coordinatePoint x theta) *
          ∏ i, qCoordinateChainFactor z w r i (coordinatePoint x theta)) =ᵐ[
          volume.restrict (Icc left right)] (0 : ℝ → ℝ) := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        rw [qCoordinateChainProduct_eq_zero_of_inactive hU hz (hseg x hx) w
          (topResidualWords_properties m w hw).1 r hactive, mul_zero]
        rfl
      rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
      positivity

theorem qCoordinateChainSum_slice_eLpNorm_two_active
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor C : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3) (hC : 0 ≤ C)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, QActiveComponents w r → ∀ x ∈ Icc left right,
      |qCoordinateChainCoefficient g z w r (coordinatePoint x theta)| ≤ C)
    (ws : List ChainWord) (hws : ∀ w ∈ ws, w ∈ topResidualWords m) :
    eLpNorm (fun x => qCoordinateChainSum g z ws (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qChainSliceBudget C lengthFloor left right H ws := by
  induction ws with
  | nil =>
      change eLpNorm (0 : ℝ → ℝ) 2 (volume.restrict (Icc left right)) ≤ 0
      simp
  | cons w ws ih =>
      have hw := hws w List.mem_cons_self
      have ht := qCoordinateChainTerm_slice_eLpNorm_two_active hg hU hz hxx hseg hlength hwidth hm hC
        hL2 hw (hcoeff w hw)
      have hs := ih (fun v hv => hws v (List.mem_cons_of_mem _ hv))
      change eLpNorm (fun x => qCoordinateChainTerm g z w (coordinatePoint x theta) +
        qCoordinateChainSum g z ws (coordinatePoint x theta)) 2 (volume.restrict (Icc left right)) ≤
          qWordSliceBudget C lengthFloor left right H w + qChainSliceBudget C lengthFloor left right H ws
      exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add ht hs)

theorem actualQHighRemainder_slice_eLpNorm_two_active
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor C Cfirst : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3) (hC : 0 ≤ C) (hCfirst : 0 ≤ Cfirst)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, QActiveComponents w r → ∀ x ∈ Icc left right,
      |qCoordinateChainCoefficient g z w r (coordinatePoint x theta)| ≤ C)
    (hfirst2 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 2) (coordinatePoint x theta)| ≤ Cfirst)
    (hfirst3 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 3) (coordinatePoint x theta)| ≤ Cfirst) :
    eLpNorm (fun x => actualQHighRemainder g z m (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qRemainderSliceBudget C Cfirst lengthFloor left right H m := by
  have hs := qCoordinateChainSum_slice_eLpNorm_two_active hg hU hz hxx hseg hlength hwidth hm hC
    hL2 hcoeff (topResidualWords m) (fun _ wordMem => wordMem)
  have hp := qFirstJetPairRemainder_slice_eLpNorm_two hg hU hz hxx hseg hCfirst hL2 hfirst2 hfirst3
  have hscaled : eLpNorm (fun x => (m + 3 : ℝ) * qFirstJetPairRemainder g z (m + 2) (coordinatePoint x theta))
      2 (volume.restrict (Icc left right)) ≤ ‖(m + 3 : ℝ)‖ₑ * qPairSliceBudget Cfirst H := by
    change eLpNorm ((m + 3 : ℝ) • (fun x => qFirstJetPairRemainder g z (m + 2) (coordinatePoint x theta)))
      2 (volume.restrict (Icc left right)) ≤ _
    rw [eLpNorm_const_smul (𝕜 := ℝ) (F := ℝ)]
    exact mul_le_mul' le_rfl hp
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add hs hscaled)

end SmoothLocal.HighEquation

end

end OAI
