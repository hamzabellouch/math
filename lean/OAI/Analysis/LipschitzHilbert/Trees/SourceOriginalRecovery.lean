import OAI.Analysis.LipschitzHilbert.Estimates.OriginalRecovery
import OAI.Analysis.LipschitzHilbert.Trees.SourceFixedException
import OAI.Analysis.LipschitzHilbert.Trees.SourceMovingException

namespace OAI

/-! Recover the original adjoint sum with the manuscript's fixed and
moving exceptional-area budgets. The common good set precedes all
translations, and only the boundary error is averaged. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace LipschitzHilbert

theorem eventually_original_recovery (q m decay : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (X E : Type*) [MeasurableSpace X] [NormedAddCommGroup E]
      (μ : Measure X) (P Q : X → E) (W : ℝ → X → E), MemLp P 2 μ →
    ∀ (F source Z0 : Set X) (Z : ℝ → Set X),
      MeasurableSet F → MeasurableSet Z0 → (∀ origin, MeasurableSet (Z origin)) →
      μ F ≠ ∞ → Z0 ⊆ F → (∀ origin, Z origin ⊆ Z0) →
    ∀ N : ℝ, 0 ≤ N → μ.real source = N^2*μ.real F → N ≤ Real.exp (2*L) →
      (∫ x, ‖P x‖^2 ∂μ) ≤ (L^q)^2*μ.real source →
      μ.real (F\Z0) ≤ (L^(-q-(decay+1)))^2*μ.real F →
      (∀ origin, μ.real (Z0\Z origin) ≤ L^m*μ.real source*Real.exp (-9*L)) →
      IntegrableOn (fun x => ‖P x-Q x‖) Z0 μ →
      (∀ origin, IntegrableOn (fun x => ‖Q x-W origin x‖) Z0 μ) →
      (∀ origin, IntegrableOn (fun x => ‖W origin x‖) (Z origin) μ) →
      (∫ x in Z0, ‖P x-Q x‖ ∂μ) ≤ L^(-(decay+1))*N*μ.real F →
      (∀ origin, (∫ x in Z origin, ‖W origin x‖ ∂μ) ≤ L^(-(decay+1))*N*μ.real F) →
    ∀ R : ℝ, 0 < R →
      IntervalIntegrable (fun origin => ∫ x in Z0, ‖Q x-W origin x‖ ∂μ) volume 0 R →
      (∫ origin in (0:ℝ)..R, ∫ x in Z0, ‖Q x-W origin x‖ ∂μ)/R ≤
        L^(-(decay+1))*N*μ.real F →
      (∫ x in F, ‖P x‖ ∂μ) ≤ L^(-decay)*N*μ.real F := by
  filter_upwards [eventually_ge_atTop (5:ℝ),
    eventually_original_moving_exception q m (decay+1)] with L hL hmove
  intro X E _ _ μ P Q W hP F source Z0 Z hF hZ0 hZ hFfin hZ0F hZZ0
    N hN hratio hNexp henergy hfixedArea hmoveArea hPQ hQW hW hmask hcentral
    R hR herror hboundary
  have hL0 : 0 < L := by linarith
  have hPint := (integral_norm_on_set_le_l2 μ P hP hFfin).1
  have hfixedFin : μ (F\Z0) ≠ ∞ := ne_top_of_le_ne_top hFfin (measure_mono sdiff_subset)
  have hfixed := original_fixed_exception_cost μ P hP (F\Z0) F hfixedFin
    L q (decay+1) N hL0 hN (by simpa only [hratio] using henergy) hfixedArea
  have hmoving (origin : ℝ) :
      (∫ x in Z0\Z origin, ‖P x‖ ∂μ) ≤ L^(-(decay+1))*N*μ.real F := by
    have hfin : μ (Z0\Z origin) ≠ ∞ := ne_top_of_le_ne_top hFfin
      (measure_mono (fun x hx => hZ0F hx.1))
    exact (hmove X E μ P hP (Z0\Z origin) source F hfin N hN hratio hNexp
      henergy (hmoveArea origin)).2
  let budget := L^(-(decay+1))*N*μ.real F
  have hr := recover_original_from_moving_good μ F Z0 Z hF hZ0 hZ hZ0F hZZ0
    P Q W hPint hPQ hQW hW R budget budget budget budget budget hR
    hfixed.2 hmoving hmask hcentral herror hboundary
  have hpower : L^(-(decay+1))*L = L^(-decay) := by
    calc
      _ = L^(-(decay+1))*L^(1:ℝ) := by rw [Real.rpow_one]
      _ = L^(-(decay+1)+1) := (Real.rpow_add hL0 _ _).symm
      _ = _ := by congr 1; ring
  have hcoef : 5*L^(-(decay+1)) ≤ L^(-decay) := by
    calc
      _ ≤ L^(-(decay+1))*L := by nlinarith [Real.rpow_nonneg hL0.le (-(decay+1))]
      _ = _ := hpower
  calc
    _ ≤ budget+budget+budget+budget+budget := hr
    _ = (5*L^(-(decay+1)))*N*μ.real F := by dsimp only [budget]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hN) measureReal_nonneg

end LipschitzHilbert

end

end OAI
