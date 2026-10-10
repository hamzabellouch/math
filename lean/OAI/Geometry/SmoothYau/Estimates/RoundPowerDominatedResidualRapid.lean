import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.RoundPowerWeightedChartJets
import OAI.Geometry.SmoothYau.Spectrum.TransverseZeroKernel

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
namespace YauCounterexamples
local instance roundPowerDominatedResidualRapidFinrank :
    Fact (Module.finrank ℝ (Euclidean (3+1)) = 3+1) := ⟨by simp [Euclidean]⟩

theorem roundPower_dominated_residual_rapid_decay
    (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (a b : Euclidean (3+1)) (p : Sphere 3) {K : Set (Euclidean 3)}
    (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean 3) p).target)
    (φ : Euclidean 3 → ℝ) (hφ : ContinuousOn φ K) (h P : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hdom : ∀ y ∈ K, ‖roundPlanarChart a b p y‖ ≤ ρ*Real.exp (φ y)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j
        ((fun z => laplaceBeltrami g (roundPower a b n) z +
          (n:ℝ)*((n:ℝ)+2)*roundPower a b n z) ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤
        ((n:ℝ)^P)⁻¹*Real.exp ((n:ℝ)*φ y) := by
  obtain ⟨A,hA,hAj⟩ := roundPower_dominated_chart_jets a b p hK hKO φ hφ (h+2) hρ hdom
  obtain ⟨L,hL,hLj⟩ := laplaceBeltrami_residual_small_jets_on_compact g p hK hKO h
  let D := (L+3)*A
  have hD : 0 < D := by dsimp [D]; positivity
  have ht : Tendsto (fun n : ℕ => D*((n:ℝ)^(h+4+P)*ρ^n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one (h+4+P) hρ.le hρ1).const_mul D
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds zero_lt_one))
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro n hn y hy j hj
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  have hnpos : 0 < (n:ℝ) := zero_lt_one.trans_le hnR
  have hsmall : D*(n:ℝ)^(h+4)*ρ^n ≤ ((n:ℝ)^P)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ (pow_pos hnpos P)).mpr
    have he : D*(n:ℝ)^(h+4)*ρ^n*(n:ℝ)^P = D*((n:ℝ)^(h+4+P)*ρ^n) := by
      rw [pow_add]; ring
    rw [he]
    exact (hN n ((le_max_left _ _).trans hn)).le
  let ε := A*(n:ℝ)^(h+2)*ρ^n*Real.exp ((n:ℝ)*φ y)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hraw : ∀ k ≤ h+2,
      ‖iteratedFDeriv ℝ k (roundPower a b n ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤ ε := by
    intro k hk
    apply (hAj n y hy k hk).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hnR hk) hA.le)
        (pow_nonneg hρ.le n)) (Real.exp_pos _).le
  have hjb := hLj (roundPower a b n) (roundPower_smooth a b n) y hy ε
    ((n:ℝ)*((n:ℝ)+2)) hε (by positivity) hraw j hj
  have hquad : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hnR) hnpos.le]
  have hLbound : L ≤ L*(n:ℝ)^2 := le_mul_of_one_le_right hL.le (one_le_pow₀ hnR)
  have hLam : L+(n:ℝ)*((n:ℝ)+2) ≤ (L+3)*(n:ℝ)^2 := by nlinarith
  apply hjb.trans
  calc
    _ ≤ ((L+3)*(n:ℝ)^2)*ε := mul_le_mul_of_nonneg_right hLam hε
    _ = (D*(n:ℝ)^(h+4)*ρ^n)*Real.exp ((n:ℝ)*φ y) := by
      dsimp [D,ε]
      rw [show h+4 = 2+(h+2) by omega,pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
end YauCounterexamples

end

end OAI
