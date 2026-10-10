import OAI.Geometry.IsometricImmersion.Energy.ActualRemainderL2
import OAI.Geometry.IsometricImmersion.Metrics.StateCoefficientTube
import OAI.Geometry.IsometricImmersion.Immersions.HeightCoefficientClosedBounds
import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetNorm

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem stateCompactTube_finite_P_bounds
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) (ell : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ ell, ∀ w ∈ stateCompactTube g S M c,
      ‖iteratedFDeriv ℝ k (sixVariableP g) w‖ ≤ C := by
  classical
  have hk : ∀ k : Fin (ell + 1), ∃ A : ℝ,
      ∀ w ∈ stateCompactTube g S M c, ‖iteratedFDeriv ℝ k.val (sixVariableP g) w‖ ≤ A :=
    fun k => stateCompactTube_derivative_bound hg hU hS hSU M hc
      (sixVariableP_contDiffOn hg hU) k.val
  choose A hA using hk
  refine ⟨∑ k : Fin (ell + 1), |A k|,
    Finset.sum_nonneg (fun index _ => abs_nonneg (A index)), ?_⟩
  intro k hk w hw
  let j : Fin (ell + 1) := ⟨k, by omega⟩
  exact (hA j w hw).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun index _ => abs_nonneg (A index)) (Finset.mem_univ j)))

theorem coordinateChainCoefficient_abs_le_full_derivative
    (g : MetricField) (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (p : Coord) :
    |coordinateChainCoefficient g z w r p| ≤
      ‖iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p)‖ := by
  have h := (iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p)).le_opNorm
    (fun i => Pi.single (r i) (1 : ℝ))
  simpa only [coordinateChainCoefficient, Pi.norm_single, norm_one,
    Finset.prod_const_one, mul_one, Real.norm_eq_abs] using h

theorem solutionJet_coord_bound_on_modelSquare
    {z : Coord → ℝ} {Z : ℝ} (hzB : CoordinateBound z modelSquare 2 Z)
    {p : Coord} (hp : p ∈ modelSquare) (i : Fin 6) :
    |solutionJet z p i| ≤ max 3 Z := by
  fin_cases i
  · exact (abs_le.mpr ⟨hp.1 0, hp.2 0⟩).trans (le_max_left 3 Z)
  · exact (abs_le.mpr ⟨hp.1 1, hp.2 1⟩).trans (le_max_left 3 Z)
  · exact (hzB [0] (by norm_num) p hp).trans (le_max_right 3 Z)
  · exact (hzB [1] (by norm_num) p hp).trans (le_max_right 3 Z)
  · exact (hzB [0, 1] (by norm_num) p hp).trans (le_max_right 3 Z)
  · exact (hzB [1, 1] (by norm_num) p hp).trans (le_max_right 3 Z)

theorem solutionJet_mem_compactTube_of_low_bound
    (g : MetricField) {z : Coord → ℝ} {Z c : ℝ}
    (hzB : CoordinateBound z modelSquare 2 Z)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|)
    {p : Coord} (hp : p ∈ modelSquare) :
    solutionJet z p ∈ stateCompactTube g modelSquare (max 3 Z) c := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa only [Set.mem_preimage, statePoint_solutionJet] using hp
  · constructor <;> intro i
    · exact (abs_le.mp (solutionJet_coord_bound_on_modelSquare hzB hp i)).1
    · exact (abs_le.mp (solutionJet_coord_bound_on_modelSquare hzB hp i)).2
  · simpa only [Set.mem_preimage, Set.mem_Ici, stateDenominator_solutionJet] using hyy p hp

theorem exists_uniform_outer_remainder_coefficient_bound
    {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (Z : ℝ) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Coord → ℝ,
      CoordinateBound z modelSquare 2 Z →
      (∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) →
      ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ modelSquare,
        |coordinateChainCoefficient g z w r p| ≤ C := by
  obtain ⟨C, hC, hCP⟩ := stateCompactTube_finite_P_bounds hg hU modelSquare_isCompact hSU
    (max 3 Z) hc (m + 3)
  refine ⟨C, hC, ?_⟩
  intro z hzB hyy w hw r p hp
  exact (coordinateChainCoefficient_abs_le_full_derivative g z w r p).trans
    (hCP w.arity (residual_scalar_factor_orders hw r).2 (solutionJet z p)
      (solutionJet_mem_compactTube_of_low_bound g hzB hyy hp))

theorem exists_uniform_remainder_coefficients_original_data
    {g : MetricField} {U : Set Coord} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
      CoordinateBound z modelSquare 5 Z →
      (∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) →
      ∃ W : Set Coord, IsOpen W ∧ modelSquare ⊆ W ∧ W ⊆ U ∧
        (∀ p ∈ W, covHessian g z p 1 1 ≠ 0) ∧
        (∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ modelSquare,
          |coordinateChainCoefficient g z w r p| ≤ C) ∧
        (∀ i : Fin 2, ∀ p ∈ modelSquare,
          |coordPartial 1 (heightPFirst g z i) p| ≤ heightPFirstBound G Z d c) := by
  obtain ⟨C, hC, houter⟩ := exists_uniform_outer_remainder_coefficient_bound hg hU hSU Z hc m
  refine ⟨C, hC, ?_⟩
  intro z hz hzB hyy
  obtain ⟨W, hW, hSW, hWU, hne, _, _, _, hfirstB, _⟩ :=
    exists_open_low_height_coefficients hg hU hSU hz hG hZ hd hc hgB hzB hdet hyy
  refine ⟨W, hW, hSW, hWU, hne, houter z (hzB.mono (by norm_num) le_rfl) hyy, ?_⟩
  intro i p hp
  exact hfirstB i [1] (by norm_num) p hp

theorem exists_uniform_actualHighRemainder_bound_original_data
    {g : MetricField} {U : Set Coord} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
      CoordinateBound z modelSquare 5 Z →
      (∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) →
      ∀ V : Set Coord, MeasurableSet V → V ⊆ modelSquare → volume V < (⊤ : ℝ≥0∞) →
      ∀ B : ℝ, 1 ≤ B → ∀ H : ℝ≥0,
      (∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
        ∀ p ∈ V, |heightStateFactor z n j p| ≤ B) →
      (∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
        eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞)) →
      eLpNorm (actualHighRemainder g z m) 2 (volume.restrict V) ≤
        actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m ∧
      actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m < (⊤ : ℝ≥0∞) ∧
      MemLp (actualHighRemainder g z m) 2 (volume.restrict V) := by
  obtain ⟨C, hC, hcoeff⟩ := exists_uniform_remainder_coefficients_original_data
    hg hU hSU hG hZ hd hc hgB hdet m
  refine ⟨C, hC, ?_⟩
  intro z hz hzB hyy V hV hVS hVfinite B hB H hlow hheight
  obtain ⟨W, hW, hSW, hWU, hne, houter, hfirst⟩ := hcoeff z hz hzB hyy
  have hgW : SmoothPositiveOn g W :=
    ⟨fun i j => (hg.1 i j).mono hWU, fun p hp => hg.2 p (hWU hp)⟩
  have hVW : V ⊆ W := hVS.trans hSW
  have hCfirst := heightPFirstBound_nonneg hG hZ hd hc
  have ho : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C :=
    fun w hw r p hp => houter w hw r p (hVS hp)
  have hf : ∀ i : Fin 2, ∀ p ∈ V,
      |coordPartial 1 (heightPFirst g z i) p| ≤ heightPFirstBound G Z d c :=
    fun i p hp => hfirst i p (hVS hp)
  exact ⟨actualHighRemainder_eLpNorm_two hgW hW (hz.mono hWU) hne hV hVW hm hC hCfirst hB
      hlow hheight ho hf,
    actualHighRemainderL2Budget_lt_top C (heightPFirstBound G Z d c) B H hVfinite m,
    actualHighRemainder_memLp_two hgW hW (hz.mono hWU) hne hV hVW hVfinite hm hC hCfirst hB
      hlow hheight ho hf⟩

theorem exists_uniform_actualHighRemainder_bound_frechet_data
    {g : MetricField} {U : Set Coord} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
      (∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) →
      (∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) →
      ∀ V : Set Coord, MeasurableSet V → V ⊆ modelSquare → volume V < (⊤ : ℝ≥0∞) →
      ∀ B : ℝ, 1 ≤ B → ∀ H : ℝ≥0,
      (∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
        ∀ p ∈ V, |heightStateFactor z n j p| ≤ B) →
      (∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
        eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞)) →
      eLpNorm (actualHighRemainder g z m) 2 (volume.restrict V) ≤
        actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m ∧
      actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m < (⊤ : ℝ≥0∞) ∧
      MemLp (actualHighRemainder g z m) 2 (volume.restrict V) := by
  have hgCoord (i j : Fin 2) : CoordinateBound (fun p => g p i j) modelSquare 4 G :=
    coordinateBound_of_frechet_bounds (hg.1 i j) hU hSU (hgB i j)
  obtain ⟨C, hC, hbound⟩ := exists_uniform_actualHighRemainder_bound_original_data
    hg hU hSU hG hZ hd hc hgCoord hdet m hm
  refine ⟨C, hC, ?_⟩
  intro z hz hzB hyy V hV hVS hVfinite B hB H hlow hheight
  exact hbound z hz (coordinateBound_five_of_frechet_eight hz hU hSU hzB)
    hyy V hV hVS hVfinite B hB H hlow hheight

end SmoothLocal.HighEquation

end

end OAI
