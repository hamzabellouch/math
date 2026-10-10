import OAI.Geometry.SurfaceImmersion.Correction.AnchoredSmoothedIncrement
import OAI.Geometry.SurfaceImmersion.Correction.ActualSmoothedStep

namespace OAI

/-! Actual normalized correction steps with an explicit fast-map neighborhood. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry MetricGoodPhaseData
local instance anchoredActualFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance anchoredActualFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance anchoredActualDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance anchoredActualDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance anchoredActualSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance anchoredActualSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem anchored_actual_step (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ z₀ a D K : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧ 0 ≤ K ∧
    ∀ r : ℕ, ∃ T : ℝ, 0 ≤ T ∧
    ∀ (q : ℕ) (Budget : ℝ → ℝ), HasPolynomialBound Budget →
    ∃ e : ℕ, ∃ E : ℝ, ∃ P Q : ℕ → ℝ → ℝ, ∃ Dm Em : ℕ → ℝ, 1 ≤ E ∧
      (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (Q m)) ∧
      (∀ m, 0 ≤ Dm m) ∧ (∀ m, 0 ≤ Em m) ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
    ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
    ∀ δ δ' t s τ : ℝ, 0 < δ → 0 < δ' → δ' ≤ δ →
      0 < t → t ≤ 1 → 0 < s → s ≤ t → 0 < τ → τ ≤ s → δ ≤ τ →
      τ/s ≤ min 1 ((a-a/2)/(2*(E*(z⁻¹)^e))) →
      A.InputBound t r (Budget z⁻¹) G (normalizedTensorDefect g.inner δ G) →
      A.WeightedBound 1 2 ((z^4/D)/4) (G-F) →
      (∀ x, ‖A.tensorEncode (normalizedTensorDefect g.inner δ G) x-A.tensorEncode g.inner x‖ ≤ a/8) →
      T*(Budget z⁻¹)*(s/t)^r ≤ min ((z^4/D)/4) (a/8) → (δ'/δ)^2*K ≤ a/8 →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m (P m z⁻¹*(δ*τ)) U) ∧
        ∀ m C, 0 ≤ C → A.InputBound t m C G (normalizedTensorDefect g.inner δ G) →
          A.TensorWeightedBound τ m
            (normalizedStepBound r q (Budget z⁻¹) (Dm m) (Em m) (P (m+1) z⁻¹) (Q m z⁻¹) C δ δ' τ s t)
            (normalizedTensorDefect g.inner δ' (G+U)-g.inner) := by
  classical
  obtain ⟨z₀,a,D,hz₀,hz₀1,ha,hD,hall⟩ := A.anchored_smoothed_increment g houter R c B b hc hB hb
  obtain ⟨K,hK,hKb⟩ := A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain 0 g.contMDiff
  have hKn (x : JetPolynomial.Base) : ‖A.tensorEncode g.inner x‖ ≤ K :=
    (A.tensorEncode_bound g.contMDiff zero_lt_one hK hKb).norm_le (mem_univ x)
  refine ⟨z₀,a,D,K,hz₀,hz₀1,ha,hD,hK,?_⟩
  intro r
  obtain ⟨T,hT,hadmissible⟩ := A.smoothed_input_admissibility r
  refine ⟨T,hT,?_⟩
  intro q Budget hBudget
  obtain ⟨e,E,P,Q,hE,hP,hQ,hbuild⟩ := hall r q Budget hBudget
  choose Dm Em hDm hEm hmetric using fun m => A.smoothed_normalized_metric_step_bound r m
  refine ⟨e,E,P,Q,Dm,Em,hE,hP,hQ,hDm,hEm,?_⟩
  intro z hz hzsmall F hF hFb hFm G hG δ δ' t s τ hδ hδ' hδ'δ ht ht1 hs hst hτ hτs hδτ
    hsmall hinput hnear hHnear htail hratio
  have hx : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr (hzsmall.trans hz₀1)
  let H := normalizedTensorDefect g.inner δ G
  have hH := A.normalizedTensorDefect_smooth g.contMDiff δ hG
  have hsym : ∀ y v w, H y v w = H y w v := by
    intro y v w
    change (δ^2)⁻¹*(g.inner y v w-inducedTensor G y v w) =
      (δ^2)⁻¹*(g.inner y w v-inducedTensor G y w v)
    rw [g.symm y v w,inducedTensor_symmetric G y v w]
  have hρ : 0 < z^4/D := div_pos (pow_pos hz 4) (zero_lt_one.trans_le hD)
  have had := hadmissible g F G H (z^4/D) a ((z^4/D)/4) (Budget z⁻¹) t s ((δ'/δ)^2) K
    hρ ha (hBudget.nonneg hx) hs hst ht1 hF hG hH hinput hnear le_rfl hHnear htail
    (sq_nonneg _) hKn hratio
  have hsnear : A.WeightedBound 1 2 (z^4/D) (A.smooth r s G-F) :=
    fun i => (had.1 i).mono_const (by linarith)
  obtain ⟨U,hU,hUB,hUE⟩ := hbuild z hz hzsmall F hF hFb hFm G H hG hH hsym t s ht ht1 hs
    (hst.trans ht1) hinput hsnear δ δ' τ hδ hδ'.le hδ'δ hτ hτs hδτ hsmall had.2
  refine ⟨U,hU,hUB,?_⟩
  intro m C hC hCm
  exact hmetric m g.inner g.contMDiff G U hG hU δ δ' τ s t (Budget z⁻¹) C
    (P (m+1) z⁻¹*(δ*τ)) (Q m z⁻¹*(δ*(τ/s)^(q+1)+δ^3/τ))
    hδ.ne' hδ'.ne' hτ hτs hst ht1 (hBudget.nonneg hx) hC
    (mul_nonneg ((hP _).nonneg hx) (mul_nonneg hδ.le hτ.le)) hinput hCm (hUB (m+1)) (hUE m)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
