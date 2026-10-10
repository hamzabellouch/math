import OAI.Probability.SLE.Loewner.LoewnerTipHullApproximation
import OAI.Probability.SLE.Loewner.LoewnerCompactDriverNeighborhood

namespace OAI

/-! A perturbed hull near an interior reference tip must be visited by
the actual trace: a surviving point in the same connected ball rules out
the possibility that the ball is entirely swallowed. -/
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge

lemma trace_meets_connected_region
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0) {S : Set ℂ}
    (hS : IsPreconnected S) (hSH : S ⊆ upperHalfPlane)
    {w : ℂ} (hwS : w ∈ S) (hwD : w ∈ survivingDomain γ T)
    (hnot : ¬ S ⊆ survivingDomain γ T) :
    ∃ t ∈ Icc 0 T, γ t ∈ S := by
  by_contra hn
  push Not at hn
  have hf : S ⊆ upperHalfPlane \ (γ '' Icc 0 T) := by
    intro z hz
    refine ⟨hSH hz,?_⟩
    rintro ⟨t,ht,rfl⟩
    exact hn t ht hz
  apply hnot
  intro z hz
  have hc := hS.subset_connectedComponentIn hwS hf hz
  refine ⟨hf hz,?_⟩
  rw [← connectedComponentIn_eq hc]
  exact hwD.2

lemma ball_subset_halfPlane {q : ℂ} {r : ℝ} (hr : r ≤ q.im) :
    ball q r ⊆ upperHalfPlane := by
  intro z hz
  have hd : ‖z-q‖ < r := by simpa only [mem_ball,dist_eq_norm] using hz
  have hi := (abs_lt.mp ((Complex.abs_im_le_norm (z-q)).trans_lt hd)).1
  simp only [Complex.sub_im] at hi
  change 0 < z.im
  linarith

theorem driver_neighborhood_visits_tip
    {V : ℝ≥0 → ℝ} {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0)
    {r : ℝ} (hr : 0 < r) (hrH : r ≤ (β T).im)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ survivingDomain β T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
      (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
      (∀ t ∈ Icc 0 T, |U t-V t| ≤ δ) →
      K ⊆ survivingDomain γ T ∧ ∃ t ∈ Icc 0 T, γ t ∈ ball (β T) r := by
  have he : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < y ∧
      J T ((V T : ℂ)+(y : ℂ)*Complex.I) ∈ ball (β T) r := by
    filter_upwards [self_mem_nhdsWithin,
      (hv.2.2.2.2.2.2.2.2.2.2.2.2 T).eventually (ball_mem_nhds _ hr)] with y hy hb
    exact ⟨hy,hb⟩
  obtain ⟨y,hy,hyw⟩ := he.exists
  let w := J T ((V T : ℂ)+(y : ℂ)*Complex.I)
  have hw : w ∈ survivingDomain β T := hv.2.2.2.2.2.2.1 T
    (by simpa [upperHalfPlane] using hy)
  obtain ⟨δ₁,hδ₁,hkeep⟩ := driver_neighborhood_preserves_compact hv T hK hKD
  obtain ⟨δ₂,hδ₂,hwkeep⟩ := driver_neighborhood_preserves_compact hv T
    (isCompact_singleton : IsCompact ({w} : Set ℂ)) (singleton_subset_iff.mpr hw)
  obtain ⟨δ₃,hδ₃,hhit⟩ := driver_neighborhood_hits_tip_hull hv T hr
  refine ⟨min δ₁ (min δ₂ δ₃),lt_min hδ₁ (lt_min hδ₂ hδ₃),?_⟩
  intro U γ G F h hclose
  have h₁ : ∀ t ∈ Icc 0 T, |U t-V t| ≤ δ₁ :=
    fun t ht => (hclose t ht).trans (min_le_left _ _)
  have h₂ : ∀ t ∈ Icc 0 T, |U t-V t| ≤ δ₂ :=
    fun t ht => (hclose t ht).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h₃ : ∀ t ∈ Icc 0 T, |U t-V t| ≤ δ₃ :=
    fun t ht => (hclose t ht).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨hkeep U γ G F h h₁,?_⟩
  exact trace_meets_connected_region γ T (convex_ball _ _).isPreconnected
    (ball_subset_halfPlane hrH) hyw
    ((hwkeep U γ G F h h₂) (mem_singleton w)) (hhit U γ G F h h₃)

end SLEExactGauge

end

end OAI
