import OAI.Geometry.IsometricImmersion.Darboux.QResidualFactors

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Analytic

def qWordSliceBudget (C lengthFloor left right : ℝ) (H : ℝ≥0) (w : ChainWord) : ℝ≥0∞ :=
  ∑ _r : Fin w.arity → Fin 6,
    ‖C‖ₑ * spatialProductL2Budget lengthFloor left right H w.arity

def qChainSliceBudget (C lengthFloor left right : ℝ) (H : ℝ≥0)
    (ws : List ChainWord) : ℝ≥0∞ :=
  (ws.map (qWordSliceBudget C lengthFloor left right H)).sum

def qPairSliceBudget (Cfirst : ℝ) (H : ℝ≥0) : ℝ≥0∞ :=
  ‖Cfirst‖ₑ * (H : ℝ≥0∞) + ‖Cfirst‖ₑ * (H : ℝ≥0∞)

def qRemainderSliceBudget (C Cfirst lengthFloor left right : ℝ) (H : ℝ≥0)
    (m : ℕ) : ℝ≥0∞ :=
  qChainSliceBudget C lengthFloor left right H (topResidualWords m) +
    ‖(m + 3 : ℝ)‖ₑ * qPairSliceBudget Cfirst H

theorem qWordSliceBudget_lt_top (C lengthFloor left right : ℝ) (H : ℝ≥0) (w : ChainWord) :
    qWordSliceBudget C lengthFloor left right H w < (⊤ : ℝ≥0∞) := by
  unfold qWordSliceBudget
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.mul_lt_top (by finiteness)
    (spatialProductL2Budget_lt_top lengthFloor left right H w.arity))

theorem qChainSliceBudget_lt_top (C lengthFloor left right : ℝ) (H : ℝ≥0)
    (ws : List ChainWord) : qChainSliceBudget C lengthFloor left right H ws < (⊤ : ℝ≥0∞) := by
  induction ws with
  | nil => simp [qChainSliceBudget]
  | cons w ws ih =>
      exact ENNReal.add_lt_top.mpr ⟨qWordSliceBudget_lt_top C lengthFloor left right H w, ih⟩

theorem qRemainderSliceBudget_lt_top (C Cfirst lengthFloor left right : ℝ)
    (H : ℝ≥0) (m : ℕ) : qRemainderSliceBudget C Cfirst lengthFloor left right H m < (⊤ : ℝ≥0∞) := by
  unfold qRemainderSliceBudget qPairSliceBudget
  exact ENNReal.add_lt_top.mpr
    ⟨qChainSliceBudget_lt_top C lengthFloor left right H (topResidualWords m), by finiteness⟩

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem qCoordinateScalarTerm_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (w : ChainWord) (r : Fin w.arity → Fin 6) :
    ContinuousOn (fun p => qCoordinateChainCoefficient g z w r p *
      ∏ i, qCoordinateChainFactor z w r i p) U :=
  (qCoordinateChainCoefficient_continuousOn hg hU hz hxx w r).mul
    (continuousOn_finsetProd Finset.univ (fun i _ =>
      qCoordinateChainFactor_continuousOn hU hz w r i))

theorem qCoordinateChainTerm_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (w : ChainWord) :
    ContinuousOn (qCoordinateChainTerm g z w) U := by
  have he : qCoordinateChainTerm g z w = fun p => ∑ r : Fin w.arity → Fin 6,
      qCoordinateChainCoefficient g z w r p * ∏ i, qCoordinateChainFactor z w r i p :=
    funext (qCoordinateChainTerm_scalar_expansion g z w)
  rw [he]
  exact continuousOn_finsetSum Finset.univ
    (fun r _ => qCoordinateScalarTerm_continuousOn hg hU hz hxx w r)

theorem qCoordinateChainSum_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (ws : List ChainWord) :
    ContinuousOn (qCoordinateChainSum g z ws) U := by
  induction ws with
  | nil => exact continuousOn_const
  | cons w ws ih => exact (qCoordinateChainTerm_continuousOn hg hU hz hxx w).add ih

theorem q_residual_product_eLpNorm_two
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {theta left right lengthFloor : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    {w : ChainWord} (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) :
    eLpNorm (fun x => ∏ i, qCoordinateChainFactor z w r i (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤
        spatialProductL2Budget lengthFloor left right H w.arity := by
  classical
  let B := spatialLowFactorBound lengthFloor H
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  obtain ⟨hpos, _, horders⟩ := topResidualWords_properties m w hw
  have hproductMeas := (smooth_slice_memLp_two
    (continuousOn_finsetProd Finset.univ (fun index _ =>
      qCoordinateChainFactor_continuousOn hU hz w r index)) hseg).aestronglyMeasurable
  have hfactorOrders := (q_residual_factor_orders hw r).1
  have hlow (i : Fin w.arity) (hi : qChainFactorOrder w r i + 1 ≤ m + 2)
      (x : ℝ) (hx : x ∈ Icc left right) :
      ‖qCoordinateChainFactor z w r i (coordinatePoint x theta)‖ ≤ B :=
    q_state_factor_low_bound hU hz hseg hlength hwidth hL2
      (w.order i) (hpos i) (r i) hi hx
  by_cases hh : ∃ j, m + 2 ≤ qChainFactorOrder w r j
  · obtain ⟨j, hj⟩ := hh
    have hb (i : Fin w.arity) (hi : i ∈ (Finset.univ : Finset (Fin w.arity)).erase j)
        (x : ℝ) (hx : x ∈ Icc left right) :
        ‖qCoordinateChainFactor z w r i (coordinatePoint x theta)‖ ≤ B := by
      apply hlow i _ x hx
      have hnot : ¬ m + 2 ≤ qChainFactorOrder w r i := fun hie =>
        (Finset.mem_erase.mp hi).1 (q_residual_high_unique hm hw r hie hj)
      omega
    have hjL2 : eLpNorm (fun x => qCoordinateChainFactor z w r j (coordinatePoint x theta)) 2
        (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞) :=
      q_state_factor_high_eLpNorm hU hz hseg hL2 (w.order j) (hpos j)
        (by have ho := horders j; omega) (r j) hj (hfactorOrders j)
    have hprod := finite_product_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (fun i x => qCoordinateChainFactor z w r i (coordinatePoint x theta))
      (Finset.mem_univ j) hB0 measurableSet_Icc hb hproductMeas
    have hcard : ((Finset.univ : Finset (Fin w.arity)).erase j).card ≤ w.arity := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.erase_subset j (Finset.univ : Finset (Fin w.arity)))
    have hpow : ‖B ^ ((Finset.univ : Finset (Fin w.arity)).erase j).card‖ₑ ≤ ‖B ^ w.arity‖ₑ := by
      rw [enorm_le_iff_norm_le, Real.norm_of_nonneg (pow_nonneg hB0 _),
        Real.norm_of_nonneg (pow_nonneg hB0 _)]
      exact pow_le_pow_right₀ hB1 hcard
    calc
      _ ≤ ‖B ^ ((Finset.univ : Finset (Fin w.arity)).erase j).card‖ₑ *
          eLpNorm (fun x => qCoordinateChainFactor z w r j (coordinatePoint x theta)) 2
            (volume.restrict (Icc left right)) := hprod
      _ ≤ ‖B ^ w.arity‖ₑ * (H : ℝ≥0∞) := mul_le_mul' hpow hjL2
      _ ≤ _ := mul_le_mul' le_rfl (le_add_of_nonneg_right (by positivity))
  · have hb (i : Fin w.arity) (_ : i ∈ (Finset.univ : Finset (Fin w.arity)))
        (x : ℝ) (hx : x ∈ Icc left right) :
        ‖qCoordinateChainFactor z w r i (coordinatePoint x theta)‖ ≤ B := by
      apply hlow i _ x hx
      have hnot : ¬ m + 2 ≤ qChainFactorOrder w r i := fun hie => hh ⟨i, hie⟩
      omega
    have hprod := finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (fun i x => qCoordinateChainFactor z w r i (coordinatePoint x theta))
      hB0 measurableSet_Icc hb hproductMeas
    calc
      _ ≤ ‖B ^ w.arity‖ₑ * (volume (Icc left right)) ^ (1 / (2 : ℝ)) := by
        simpa only [Finset.card_univ, Fintype.card_fin] using hprod
      _ ≤ _ := mul_le_mul' le_rfl (le_add_of_nonneg_left (by positivity))

theorem qCoordinateChainTerm_slice_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor C : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3) (hC : 0 ≤ C)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    {w : ChainWord} (hw : w ∈ topResidualWords m)
    (hcoeff : ∀ r x, x ∈ Icc left right →
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
    exact (real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable hC (hcoeff r)
      (smooth_slice_memLp_two
        (qCoordinateScalarTerm_continuousOn hg hU hz hxx w r) hseg).aestronglyMeasurable).trans
      (mul_le_mul' le_rfl (q_residual_product_eLpNorm_two hU hz hseg hlength hwidth hm hL2 hw r))

theorem qCoordinateChainSum_slice_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor C : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3) (hC : 0 ≤ C)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r x, x ∈ Icc left right →
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
      have ht := qCoordinateChainTerm_slice_eLpNorm_two hg hU hz hxx hseg hlength hwidth hm hC
        hL2 hw (hcoeff w hw)
      have hs := ih (fun v hv => hws v (List.mem_cons_of_mem _ hv))
      change eLpNorm (fun x => qCoordinateChainTerm g z w (coordinatePoint x theta) +
        qCoordinateChainSum g z ws (coordinatePoint x theta)) 2 (volume.restrict (Icc left right)) ≤
          qWordSliceBudget C lengthFloor left right H w + qChainSliceBudget C lengthFloor left right H ws
      exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add ht hs)

theorem qFirstJetPairRemainder_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (n : ℕ) :
    ContinuousOn (qFirstJetPairRemainder g z n) U := by
  have hc (i : Fin 6) := (partial_contDiffOn (heightQCoefficient_contDiffOn hg hU hz hxx i) hU 0).continuousOn
  have hf (i : Fin 2) := (partial_contDiffOn (horizontalJet_contDiffOn hU hz n) hU i).continuousOn
  exact ((hc 2).mul (hf 0)).add ((hc 3).mul (hf 1))

theorem qFirstJetPairRemainder_slice_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right Cfirst : ℝ} {N : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U) (hCfirst : 0 ≤ Cfirst)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right N H)
    (hfirst2 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 2) (coordinatePoint x theta)| ≤ Cfirst)
    (hfirst3 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 3) (coordinatePoint x theta)| ≤ Cfirst) :
    eLpNorm (fun x => qFirstJetPairRemainder g z N (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qPairSliceBudget Cfirst H := by
  have hf (i : Fin 2) : eLpNorm (fun x => coordPartial i (horizontalJet z N) (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞) := by
    have he : (fun x => coordPartial i (horizontalJet z N) (coordinatePoint x theta)) =ᵐ[
        volume.restrict (Icc left right)] (fun x => spatialJet (spatialFirstJet z i) N (coordinatePoint x theta)) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [← horizontalJet_coordPartial hU hz i N _ (hseg x hx), horizontalJet_eq_spatialJet]
      rfl
    rw [eLpNorm_congr_ae he]
    exact hL2 i N le_rfl
  have hm (i : Fin 6) (j : Fin 2) : AEStronglyMeasurable
      (fun x => coordPartial 0 (heightQCoefficient g z i) (coordinatePoint x theta) *
        coordPartial j (horizontalJet z N) (coordinatePoint x theta))
      (volume.restrict (Icc left right)) :=
    (smooth_slice_memLp_two
      ((partial_contDiffOn (heightQCoefficient_contDiffOn hg hU hz hxx i) hU 0).continuousOn.mul
        (partial_contDiffOn (horizontalJet_contDiffOn hU hz N) hU j).continuousOn) hseg).aestronglyMeasurable
  have h0 := (real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable
    hCfirst hfirst2 (hm 2 0)).trans (mul_le_mul' le_rfl (hf 0))
  have h1 := (real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable
    hCfirst hfirst3 (hm 3 1)).trans (mul_le_mul' le_rfl (hf 1))
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add h0 h1)

theorem actualQHighRemainder_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (m : ℕ) :
    ContinuousOn (actualQHighRemainder g z m) U :=
  (qCoordinateChainSum_continuousOn hg hU hz hxx (topResidualWords m)).add
    (continuousOn_const.mul (qFirstJetPairRemainder_continuousOn hg hU hz hxx (m + 2)))

theorem actualQHighRemainder_slice_memLp_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (m : ℕ)
    {theta left right : ℝ} (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U) :
    MemLp (fun x => actualQHighRemainder g z m (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) :=
  smooth_slice_memLp_two (actualQHighRemainder_continuousOn hg hU hz hxx m) hseg

theorem actualQHighRemainder_slice_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor C Cfirst : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3) (hC : 0 ≤ C) (hCfirst : 0 ≤ Cfirst)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r x, x ∈ Icc left right →
      |qCoordinateChainCoefficient g z w r (coordinatePoint x theta)| ≤ C)
    (hfirst2 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 2) (coordinatePoint x theta)| ≤ Cfirst)
    (hfirst3 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 3) (coordinatePoint x theta)| ≤ Cfirst) :
    eLpNorm (fun x => actualQHighRemainder g z m (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qRemainderSliceBudget C Cfirst lengthFloor left right H m := by
  have hs := qCoordinateChainSum_slice_eLpNorm_two hg hU hz hxx hseg hlength hwidth hm hC
    hL2 hcoeff (topResidualWords m) (fun _ hw => hw)
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
