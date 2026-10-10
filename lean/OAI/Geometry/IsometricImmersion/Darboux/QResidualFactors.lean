import OAI.Geometry.IsometricImmersion.Darboux.QHighEquation

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def qCoordinateChainCoefficient (g : MetricField) (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ w.arity (sixVariableQ g) (qSolutionJet z p)
    (fun i => Pi.single (r i) (1 : ℝ))

def qCoordinateChainFactor (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (i : Fin w.arity) (p : Coord) : ℝ :=
  horizontalJet (qSolutionJet z) (w.order i) p (r i)

def qFirstJetOffset : Fin 6 → ℕ := ![0, 0, 0, 0, 1, 1]

def qChainFactorOrder (w : ChainWord) (r : Fin w.arity → Fin 6) (i : Fin w.arity) : ℕ :=
  w.order i + qFirstJetOffset (r i)

theorem qFirstJetOffset_le_one (i : Fin 6) : qFirstJetOffset i ≤ 1 := by
  fin_cases i <;> norm_num [qFirstJetOffset]

theorem qCoordinateChainTerm_scalar_expansion (g : MetricField) (z : Coord → ℝ)
    (w : ChainWord) (p : Coord) :
    qCoordinateChainTerm g z w p = ∑ r : Fin w.arity → Fin 6,
      qCoordinateChainCoefficient g z w r p * ∏ i, qCoordinateChainFactor z w r i p :=
  multilinear_state_components _ _

theorem coordinate_qSolutionJet_horizontal_positive
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (n : ℕ) (hn : 0 < n) :
    horizontalJet (qSolutionJet z) n p =
      ![if n = 1 then 1 else 0, 0,
        spatialJet (spatialFirstJet z 0) n p, spatialJet (spatialFirstJet z 1) n p,
        spatialJet (spatialFirstJet z 1) (n + 1) p,
        spatialJet (spatialFirstJet z 0) (n + 1) p] := by
  have h := qSolutionJetCurve_iteratedDeriv_positive hU hz
    (x := p 0) (y := p 1) (by simpa only [point_eta] using hp) n hn
  have hs := horizontalJet_slice hU (qSolutionJet_contDiffOn hU hz) (p 1) n (p 0)
    (by simpa only [point_eta] using hp)
  change iteratedDeriv n (qSolutionJetCurve z (p 1)) (p 0) = _ at hs
  rw [hs] at h
  simpa only [point_eta] using h

theorem q_residual_factor_orders {m : ℕ} {w : ChainWord}
    (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) :
    (∀ i, qChainFactorOrder w r i ≤ m + 2) ∧ w.arity ≤ m + 3 := by
  obtain ⟨hpos, htotal, hbound⟩ := topResidualWords_properties m w hw
  constructor
  · intro i
    have ho := hbound i
    have hb := qFirstJetOffset_le_one (r i)
    unfold qChainFactorOrder
    omega
  · exact htotal ▸ ChainWord.arity_le_total hpos

theorem q_residual_high_unique {m : ℕ} (hm : 8 ≤ m + 3) {w : ChainWord}
    (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) {i j : Fin w.arity}
    (hi : m + 2 ≤ qChainFactorOrder w r i) (hj : m + 2 ≤ qChainFactorOrder w r j) : i = j :=
  topResidual_high_unique hm hw (fun k => qFirstJetOffset (r k))
    (fun k => (qFirstJetOffset_le_one (r k)).trans (by norm_num)) hi hj

theorem qCoordinateChainFactor_continuousOn
    {z : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (w : ChainWord) (r : Fin w.arity → Fin 6) (i : Fin w.arity) :
    ContinuousOn (qCoordinateChainFactor z w r i) U :=
  (ContinuousLinearMap.proj (r i) : DarbouxState →L[ℝ] ℝ).continuous.comp_continuousOn
    (horizontalJet_contDiffOn hU (qSolutionJet_contDiffOn hU hz) (w.order i)).continuousOn

theorem qCoordinateChainProduct_continuousOn
    {z : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (word : ChainWord) (indices : Fin word.arity → Fin 6) :
    ContinuousOn (fun point => ∏ index, qCoordinateChainFactor z word indices index point) U :=
  continuousOn_finsetProd Finset.univ (fun index _ =>
    qCoordinateChainFactor_continuousOn hU hz word indices index)

theorem qCoordinateChainCoefficient_continuousOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (w : ChainWord) (r : Fin w.arity → Fin 6) :
    ContinuousOn (qCoordinateChainCoefficient g z w r) U := by
  intro p hp
  have hQ := sixVariableQ_contDiffAt_solutionJet hg hU hp (hxx p hp)
  have houter := (hQ.differentiableAt_iteratedFDeriv (m := w.arity)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl w.arity)).continuousAt
  have hjet := ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).continuousAt
  have heval := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.arity => DarbouxState) ℝ
    (fun i => Pi.single (r i) (1 : ℝ))).continuous.continuousAt
      (x := iteratedFDeriv ℝ w.arity (sixVariableQ g) (qSolutionJet z p))
  exact ((heval.comp houter).comp hjet).continuousWithinAt

theorem q_state_factor_low_bound
    {z : Coord → ℝ} {U : Set Coord} {theta left right lengthFloor : ℝ}
    {N : ℕ} {H : ℝ≥0}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right N H)
    (n : ℕ) (hn : 0 < n) (k : Fin 6) (horder : n + qFirstJetOffset k + 1 ≤ N)
    {x : ℝ} (hx : x ∈ Icc left right) :
    ‖horizontalJet (qSolutionJet z) n (coordinatePoint x theta) k‖ ≤
      spatialLowFactorBound lengthFloor H := by
  rw [coordinate_qSolutionJet_horizontal_positive hU hz (hseg x hx) n hn]
  have hB : 1 ≤ spatialLowFactorBound lengthFloor H := le_max_left _ _
  have hf (i : Fin 2) := partial_contDiffOn hz hU i
  have hlow (i : Fin 2) (j : ℕ) (hj : j + 1 ≤ N) :
      ‖spatialJet (spatialFirstJet z i) j (coordinatePoint x theta)‖ ≤
        spatialLowFactorBound lengthFloor H := by
    rw [Real.norm_eq_abs]
    exact (hL2.pointwise_below_top hU hf hseg hlength hwidth i j hj hx).trans (le_max_right _ _)
  fin_cases k
  · by_cases he : n = 1
    · simpa [he] using hB
    · simpa [he] using (zero_le_one.trans hB)
  · simpa using (zero_le_one.trans hB)
  · exact hlow 0 n (by simpa [qFirstJetOffset] using horder)
  · exact hlow 1 n (by simpa [qFirstJetOffset] using horder)
  · exact hlow 1 (n + 1) (by simpa [qFirstJetOffset] using horder)
  · exact hlow 0 (n + 1) (by simpa [qFirstJetOffset] using horder)

theorem q_state_factor_high_eLpNorm
    {z : Coord → ℝ} {U : Set Coord} {theta left right : ℝ} {N : ℕ} {H : ℝ≥0}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right N H)
    (n : ℕ) (hn : 0 < n) (hnlow : n < N) (k : Fin 6)
    (hhigh : N ≤ n + qFirstJetOffset k) (htop : n + qFirstJetOffset k ≤ N) :
    eLpNorm (fun x => horizontalJet (qSolutionJet z) n (coordinatePoint x theta) k) 2
      (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞) := by
  have he : (fun x => horizontalJet (qSolutionJet z) n (coordinatePoint x theta) k) =ᵐ[
      volume.restrict (Icc left right)] (fun x =>
      (![if n = 1 then 1 else 0, 0,
        spatialJet (spatialFirstJet z 0) n (coordinatePoint x theta),
        spatialJet (spatialFirstJet z 1) n (coordinatePoint x theta),
        spatialJet (spatialFirstJet z 1) (n + 1) (coordinatePoint x theta),
        spatialJet (spatialFirstJet z 0) (n + 1) (coordinatePoint x theta)] : DarbouxState) k) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact congrArg (fun w : DarbouxState => w k)
      (coordinate_qSolutionJet_horizontal_positive hU hz (hseg x hx) n hn)
  rw [eLpNorm_congr_ae he]
  fin_cases k
  · norm_num [qFirstJetOffset] at hhigh
    omega
  · norm_num [qFirstJetOffset] at hhigh
    omega
  · norm_num [qFirstJetOffset] at hhigh
    omega
  · norm_num [qFirstJetOffset] at hhigh
    omega
  · exact hL2 1 (n + 1) (by simpa [qFirstJetOffset] using htop)
  · exact hL2 0 (n + 1) (by simpa [qFirstJetOffset] using htop)

end SmoothLocal.HighEquation

end

end OAI
