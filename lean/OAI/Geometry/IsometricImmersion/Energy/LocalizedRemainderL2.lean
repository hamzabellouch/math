import OAI.Geometry.IsometricImmersion.Metrics.LocalMetricPCoefficients

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem exists_localized_actualHighRemainder_bound
    (G Z M : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hM : 0 ≤ M)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U V : Set Coord),
      SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
      (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
      ContDiffOn ℝ ∞ z U →
      (∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) →
      (∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) →
      MeasurableSet V → V ⊆ modelSquare → volume V < (⊤ : ℝ≥0∞) →
      (∀ i j k, k ≤ m + 5 → ∀ p ∈ V,
        ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ M) →
      ∀ B : ℝ, 1 ≤ B → ∀ H : ℝ≥0,
      (∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
        ∀ p ∈ V, |heightStateFactor z n j p| ≤ B) →
      (∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
        eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞)) →
      eLpNorm (actualHighRemainder g z m) 2 (volume.restrict V) ≤
        actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m ∧
      actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m < (⊤ : ℝ≥0∞) ∧
      MemLp (actualHighRemainder g z m) 2 (volume.restrict V) := by
  obtain ⟨C, hC, houter⟩ := exists_same_region_remainder_outer_bound M Z hM hd hc m
  refine ⟨C, hC, ?_⟩
  intro g z U V hg hU hSU hgB hdet hz hzB hyy hV hVS hVfinite hgHigh B hB H hlow hheight
  have hgCoord (i j : Fin 2) : CoordinateBound (fun p => g p i j) modelSquare 4 G :=
    coordinateBound_of_frechet_bounds (hg.1 i j) hU hSU (hgB i j)
  have hzCoord : CoordinateBound z modelSquare 5 Z :=
    coordinateBound_five_of_frechet_eight hz hU hSU hzB
  obtain ⟨W, hW, hSW, hWU, hne, _, _, _, hfirst, _⟩ :=
    exists_open_low_height_coefficients hg hU hSU hz hG hZ hd hc hgCoord hzCoord hdet hyy
  have hgW : SmoothPositiveOn g W :=
    ⟨fun i j => (hg.1 i j).mono hWU, fun p hp => hg.2 p (hWU hp)⟩
  have hVW : V ⊆ W := hVS.trans hSW
  have hCfirst := heightPFirstBound_nonneg hG hZ hd hc
  have ho : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C :=
    houter g z U V hg hU (hVS.trans hSU) hVS hgHigh
      ((hzCoord.mono (by norm_num) le_rfl).restrict_domain hVS)
      (fun p hp => hdet p (hVS hp)) (fun p hp => hyy p (hVS hp))
  have hf : ∀ i : Fin 2, ∀ p ∈ V,
      |coordPartial 1 (heightPFirst g z i) p| ≤ heightPFirstBound G Z d c :=
    fun i p hp => hfirst i [1] (by norm_num) p (hVS hp)
  exact ⟨actualHighRemainder_eLpNorm_two hgW hW (hz.mono hWU) hne hV hVW hm hC hCfirst hB
      hlow hheight ho hf,
    actualHighRemainderL2Budget_lt_top C (heightPFirstBound G Z d c) B H hVfinite m,
    actualHighRemainder_memLp_two hgW hW (hz.mono hWU) hne hV hVW hVfinite hm hC hCfirst hB
      hlow hheight ho hf⟩

end SmoothLocal.HighEquation

end

end OAI
