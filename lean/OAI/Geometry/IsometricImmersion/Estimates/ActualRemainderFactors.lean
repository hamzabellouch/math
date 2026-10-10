import OAI.Geometry.IsometricImmersion.Taylor.ScalarChainExpansion
import OAI.Geometry.IsometricImmersion.Energy.FiniteSumL2
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def heightStateFactor (z : Coord → ℝ) (n : ℕ) (j : Fin 4) : Coord → ℝ :=
  ![coordPartial 0 (verticalJet z n), coordPartial 1 (verticalJet z n),
    coordPartial 0 (coordPartial 1 (verticalJet z n)),
    coordPartial 1 (coordPartial 1 (verticalJet z n))] j

def heightStateBaseOrder : Fin 4 → ℕ := ![1, 1, 2, 2]
def heightComponentIndex : Fin 4 → Fin 6 := ![2, 3, 4, 5]

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

theorem heightStateFactor_contDiffOn (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (n : ℕ) (j : Fin 4) : ContDiffOn ℝ ∞ (heightStateFactor z n j) U := by
  have hv := verticalJet_contDiffOn hU hz n
  fin_cases j
  · exact partial_contDiffOn hv hU 0
  · exact partial_contDiffOn hv hU 1
  · exact partial_contDiffOn (partial_contDiffOn hv hU 1) hU 0
  · exact partial_contDiffOn (partial_contDiffOn hv hU 1) hU 1

theorem coordinateChainFactor_continuousOn (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (w : ChainWord) (r : Fin w.arity → Fin 6) (i : Fin w.arity) :
    ContinuousOn (coordinateChainFactor z w r i) U := by
  exact ((ContinuousLinearMap.proj (r i) : DarbouxState →L[ℝ] ℝ).continuous.comp_continuousOn
    (verticalJet_contDiffOn hU (solutionJet_contDiffOn hU hz) (w.order i)).continuousOn)

theorem coordinateChainCoefficient_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (w : ChainWord) (r : Fin w.arity → Fin 6) :
    ContinuousOn (coordinateChainCoefficient g z w r) U := by
  intro p hp
  have hP := sixVariableP_contDiffAt_solutionJet hg hU hp (hyy p hp)
  have houter := (hP.differentiableAt_iteratedFDeriv (m := w.arity)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl w.arity)).continuousAt
  have hjet := ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).continuousAt
  have heval := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.arity => DarbouxState) ℝ
    (fun i => Pi.single (r i) (1 : ℝ))).continuous.continuousAt
      (x := iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p))
  exact ((heval.comp houter).comp hjet).continuousWithinAt

theorem coordinateScalarTerm_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (w : ChainWord) (r : Fin w.arity → Fin 6) :
    ContinuousOn (fun p => coordinateChainCoefficient g z w r p *
      ∏ i, coordinateChainFactor z w r i p) U := by
  exact (coordinateChainCoefficient_continuousOn hg hU hz hyy w r).mul
    (continuousOn_finsetProd Finset.univ
      (fun index _ => coordinateChainFactor_continuousOn hU hz w r index))

theorem coordinateChainTerm_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (w : ChainWord) :
    ContinuousOn (coordinateChainTerm g z w) U := by
  have h := continuousOn_finsetSum Finset.univ
    (fun indices _ => coordinateScalarTerm_continuousOn hg hU hz hyy w indices)
  exact h.congr (fun point _ => coordinateChainTerm_scalar_expansion g z w point)

theorem coordinateChainSum_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (ws : List ChainWord) :
    ContinuousOn (coordinateChainSum g z ws) U :=
  continuousOn_list_sum ws (fun word _ => coordinateChainTerm_continuousOn hg hU hz hyy word)

theorem vertical_state_height_ae (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (n : ℕ) (hn : 0 < n) (j : Fin 4) :
    (fun p => verticalJet (solutionJet z) n p (heightComponentIndex j)) =ᵐ[volume.restrict V]
      heightStateFactor z n j := by
  filter_upwards [ae_restrict_mem hV] with p hp
  rw [coordinate_solutionJet_vertical_positive hU hz (hVU hp) n hn]
  fin_cases j <;> rfl

theorem vertical_state_component_low_bound
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hVU : V ⊆ U)
    {m : ℕ} {B : ℝ} (hB : 1 ≤ B)
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (n : ℕ) (hn : 0 < n) (k : Fin 6) (hk : n + stateBaseOrder k ≤ m + 1)
    {p : Coord} (hp : p ∈ V) :
    ‖verticalJet (solutionJet z) n p k‖ ≤ B := by
  rw [coordinate_solutionJet_vertical_positive hU hz (hVU hp) n hn]
  fin_cases k
  · simpa using le_trans (by norm_num : (0 : ℝ) ≤ 1) hB
  · by_cases he : n = 1
    · simpa [he] using hB
    · simpa [he] using le_trans (by norm_num : (0 : ℝ) ≤ 1) hB
  · simpa [heightStateFactor, Real.norm_eq_abs] using
      hlow n 0 (by simpa [heightStateBaseOrder, stateBaseOrder] using hk) p hp
  · simpa [heightStateFactor, Real.norm_eq_abs] using
      hlow n 1 (by simpa [heightStateBaseOrder, stateBaseOrder] using hk) p hp
  · simpa [heightStateFactor, Real.norm_eq_abs] using
      hlow n 2 (by simpa [heightStateBaseOrder, stateBaseOrder] using hk) p hp
  · simpa [heightStateFactor, Real.norm_eq_abs] using
      hlow n 3 (by simpa [heightStateBaseOrder, stateBaseOrder] using hk) p hp

theorem vertical_state_component_high_eLpNorm
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} {H : ℝ≥0}
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (n : ℕ) (hn : 0 < n) (hnlow : n ≤ m + 1) (k : Fin 6)
    (hhigh : m + 2 ≤ n + stateBaseOrder k) (htop : n + stateBaseOrder k ≤ m + 3) :
    eLpNorm (fun p => verticalJet (solutionJet z) n p k) 2 (volume.restrict V) ≤
      (H : ℝ≥0∞) := by
  fin_cases k
  · norm_num [stateBaseOrder] at hhigh
    omega
  · norm_num [stateBaseOrder] at hhigh
    omega
  · calc
      _ = eLpNorm (heightStateFactor z n 0) 2 (volume.restrict V) := by
        simpa [heightComponentIndex] using eLpNorm_congr_ae
          (vertical_state_height_ae hU hz hV hVU n hn 0)
      _ ≤ _ := hheight n 0 (by simpa [heightStateBaseOrder, stateBaseOrder] using htop)
  · calc
      _ = eLpNorm (heightStateFactor z n 1) 2 (volume.restrict V) := by
        simpa [heightComponentIndex] using eLpNorm_congr_ae
          (vertical_state_height_ae hU hz hV hVU n hn 1)
      _ ≤ _ := hheight n 1 (by simpa [heightStateBaseOrder, stateBaseOrder] using htop)
  · calc
      _ = eLpNorm (heightStateFactor z n 2) 2 (volume.restrict V) := by
        simpa [heightComponentIndex] using eLpNorm_congr_ae
          (vertical_state_height_ae hU hz hV hVU n hn 2)
      _ ≤ _ := hheight n 2 (by simpa [heightStateBaseOrder, stateBaseOrder] using htop)
  · calc
      _ = eLpNorm (heightStateFactor z n 3) 2 (volume.restrict V) := by
        simpa [heightComponentIndex] using eLpNorm_congr_ae
          (vertical_state_height_ae hU hz hV hVU n hn 3)
      _ ≤ _ := hheight n 3 (by simpa [heightStateBaseOrder, stateBaseOrder] using htop)

end SmoothLocal.HighEquation

end

end OAI
