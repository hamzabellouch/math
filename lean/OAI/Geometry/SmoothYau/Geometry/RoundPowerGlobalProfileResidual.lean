import Mathlib
import OAI.Geometry.SmoothYau.Estimates.RoundPowerDominatedResidualRapid

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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

theorem roundPower_strict_profile_residual_rapid_decay
    (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (a b : Euclidean (3+1)) (p : Sphere 3) {K : Set (Euclidean 3)}
    (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean 3) p).target)
    (φ : Euclidean 3 → ℝ) (hφ : ContinuousOn φ K) (h P : ℕ)
    (hgap : ∀ y ∈ K, roundPlanarChart a b p y ≠ 0 →
      Real.log ‖roundPlanarChart a b p y‖ < φ y) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j
        ((fun z => laplaceBeltrami g (roundPower a b n) z +
          (n:ℝ)*((n:ℝ)+2)*roundPower a b n z) ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤
        ((n:ℝ)^P)⁻¹*Real.exp ((n:ℝ)*φ y) := by
  have hr := (roundPlanarChart_smooth a b p).continuousOn.norm.mono hKO
  obtain ⟨ρ,hρ,hρ1,hrho⟩ := compact_strict_profile_ratio hK hr hφ
    (fun y _ => norm_nonneg _) (fun y hy hny => hgap y hy (norm_ne_zero_iff.mp hny))
  exact roundPower_dominated_residual_rapid_decay g a b p hK hKO φ hφ h P hρ hρ1 hrho

end

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
local instance roundPowerGlobalProfileResidualFinrankFact :
    Fact (Module.finrank ℝ (Euclidean (3+1)) = 3+1) := ⟨by simp [Euclidean]⟩

theorem roundPower_global_profile_residual_rapid_decay
    (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg₀ : ∀ (x : Sphere 3) (v w : TangentSpace 𝓘(ℝ,Euclidean 3) x),
      g₀.inner x v w = (inner ℝ : Euclidean 4 → Euclidean 4 → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4)
          (fun q : Sphere 3 => (q : Euclidean 4)) x v)
        (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4)
          (fun q : Sphere 3 => (q : Euclidean 4)) x w))
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hext : ∀ x ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) x,
      g.inner x v w = g₀.inner x v w)
    (a b : Euclidean 4) (ha : inner ℝ a a=1) (hb : inner ℝ b b=1)
    (hab : inner ℝ a b=0) (p : Sphere 3) {K : Set (Euclidean 3)}
    (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean 3) p).target)
    (φ : Euclidean 3 → ℝ) (hφ : ContinuousOn φ K) (h P : ℕ)
    (hgap : ∀ y ∈ K, (chartAt (Euclidean 3) p).symm y ∈ F →
      roundPlanarChart a b p y ≠ 0 → Real.log ‖roundPlanarChart a b p y‖ < φ y) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j
        ((fun z => laplaceBeltrami g (roundPower a b n) z +
          (n:ℝ)*((n:ℝ)+2)*roundPower a b n z) ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤
        ((n:ℝ)^P)⁻¹*Real.exp ((n:ℝ)*φ y) := by
  have hc : Continuous (chartAt (Euclidean 3) p).symm := by
    have hh := (chartAt (Euclidean 3) p).continuousOn_symm
    rwa [sphere_chart_target, continuousOn_univ] at hh
  let J := K ∩ (chartAt (Euclidean 3) p).symm ⁻¹' F
  have hJ : IsCompact J := hK.inter_right (hF.preimage hc)
  obtain ⟨N,hN,hr⟩ := roundPower_strict_profile_residual_rapid_decay g a b p hJ
    (fun y hy => hKO hy.1) φ (hφ.mono inter_subset_left) h P
    (fun y hy => hgap y hy.1 hy.2)
  refine ⟨max N 2,le_max_right _ _,?_⟩
  intro n hn y hy j hj
  by_cases hyF : (chartAt (Euclidean 3) p).symm y ∈ F
  · exact hr n ((le_max_left _ _).trans hn) y ⟨hy,hyF⟩ j hj
  · have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
    let R : Sphere 3 → ℝ := fun z => laplaceBeltrami g (roundPower a b n) z +
      (n:ℝ)*((n:ℝ)+2)*roundPower a b n z
    have hs : tsupport R ⊆ F := by
      have hs' := roundPower_residual_tsupport g g₀ hg₀ hF hext a b n hn2 ha hb hab
      have hh : (n:ℝ)+3-1 = (n:ℝ)+2 := by ring
      simpa only [Nat.cast_ofNat,hh] using hs'
    have hz : R ∘ (chartAt (Euclidean 3) p).symm =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [(hc.tendsto y).eventually (hF.isOpen_compl.mem_nhds hyF)] with z hz
      by_contra hm
      exact hz (hs (subset_closure hm))
    have hj0 := (hz.iteratedFDeriv ℝ j).eq_of_nhds
    change ‖iteratedFDeriv ℝ j (R ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤ _
    rw [hj0]
    cases j with
    | zero => simp only [norm_iteratedFDeriv_zero,norm_zero]; positivity
    | succ j => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; positivity


end YauCounterexamples
end

end OAI
