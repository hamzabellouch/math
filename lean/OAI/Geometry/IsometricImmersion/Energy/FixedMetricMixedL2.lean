import OAI.Geometry.IsometricImmersion.Energy.MixedDerivativeL2

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Analytic

theorem fixed_metric_uniform_mixed_L2_bound
    {g : MetricField} {U : Set Coord} {Z c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hc : 0 < c) (N : ℕ) (hN : 7 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
      (∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) →
      (∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) →
      (∀ p ∈ modelSquare,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      ∀ V : Set Coord, MeasurableSet V → V ⊆ interior modelSquare → volume V < (⊤ : ℝ≥0∞) →
      ∀ B : ℝ, 1 ≤ B → ∀ H Htop : ℝ≥0,
      CoordinateBound z V (N - 3) B →
      (∀ ds : List (Fin 2), ds.length ≤ N - 1 →
        eLpNorm (iteratedCoordPartial ds z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞)) →
      eLpNorm (verticalJet z N) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞) →
      eLpNorm (coordPartial 0 (verticalJet z (N - 1))) 2
        (volume.restrict V) ≤ (Htop : ℝ≥0∞) →
      (mixedXBudget C (mixedRemainderL2Budget C B H V (N - 2)) Htop N < (⊤ : ℝ≥0∞)) ∧
      ∀ ds : List (Fin 2), ds.length = N →
        eLpNorm (iteratedCoordPartial ds z) 2 (volume.restrict V) ≤
          mixedXBudget C (mixedRemainderL2Budget C B H V (N - 2)) Htop N ∧
        MemLp (iteratedCoordPartial ds z) 2 (volume.restrict V) := by
  obtain ⟨C, hC, hCP⟩ := stateCompactTube_finite_P_bounds hg hU modelSquare_isCompact hSU
    (max 3 Z) hc (N - 2)
  refine ⟨C, hC, ?_⟩
  intro z hz hzB hyy hD V hV hVS hVfinite B hB H Htop hlow hheight hv hxv
  have hz2 : CoordinateBound z modelSquare 2 Z :=
    (coordinateBound_five_of_frechet_eight hz hU hSU hzB).mono (by norm_num) le_rfl
  have hSI : interior modelSquare ⊆ U := fun p hp => hSU (interior_subset hp)
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun i j => (hg.1 i j).mono hSI, fun p hp => hg.2 p (hSI hp)⟩
  have hzI : ContDiffOn ℝ ∞ z (interior modelSquare) := hz.mono hSI
  have hyyI : ∀ p ∈ interior modelSquare, covHessian g z p 1 1 ≠ 0 :=
    fun p hp => LowQuotient.denominator_ne_zero hc hyy p (interior_subset hp)
  have hDI : ∀ p ∈ interior modelSquare,
      (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p :=
    fun p hp => hD p (interior_subset hp)
  have hP : ∀ k ≤ N - 2, ∀ p ∈ V,
      ‖iteratedFDeriv ℝ k (sixVariableP g) (solutionJet z p)‖ ≤ C := by
    intro k hk p hp
    exact hCP k hk (solutionJet z p)
      (solutionJet_mem_compactTube_of_low_bound g hz2 hyy (interior_subset (hVS hp)))
  have hfinite := mixedXBudget_lt_top C
    (mixedRemainderL2Budget_lt_top C B H hVfinite (N - 2)) Htop N
  refine ⟨hfinite, ?_⟩
  intro ds hlen
  exact ⟨all_orderN_mixed_eLpNorm_two hgI isOpen_interior hzI hDI hyyI hV hVS
      hN hC hB hP hlow hheight hv hxv ds hlen,
    all_orderN_mixed_memLp_two hgI isOpen_interior hzI hDI hyyI hV hVS hVfinite
      hN hC hB hP hlow hheight hv hxv ds hlen⟩

end SmoothLocal.HighEquation

end

end OAI
