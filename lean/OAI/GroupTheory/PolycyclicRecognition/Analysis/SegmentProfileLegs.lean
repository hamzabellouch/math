import OAI.GroupTheory.PolycyclicRecognition.Geometry.GoodRescaledFlowLegs

namespace OAI

/-! # From a single good horizontal segment to every support leg -/

noncomputable section

namespace PolycyclicRecognition

open Filter Set
open scoped Topology

/-- The slowly vanishing good-profile error can be absorbed into any fixed
positive multiple of the physical scale, uniformly over the retained sheets. -/
theorem absorb_vanishing_profile_error
    {A : Type*} (B : ℝ → Set A) (err : ℝ → A → ℝ) (ζ : ℝ → ℝ)
    (hζ : Tendsto ζ atTop (𝓝 0))
    (hbound : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ a ∈ B r, err r a ≤ r * (ζ r + η)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ a ∈ B r, err r a ≤ η * r := by
  intro η hη
  filter_upwards [hbound (η / 2) (by positivity),
    hζ.eventually (gt_mem_nhds (show (0 : ℝ) < η / 2 by positivity)),
    eventually_ge_atTop (0 : ℝ)] with r hr hz hr0 a ha
  calc
    err r a ≤ r * (ζ r + η / 2) := hr a ha
    _ ≤ η * r := by nlinarith

/-- Every shortened support leg lies in the same original horizontal
segment. In particular, one good profile controls all the chosen support
endpoints and the common pivot, without separate good sets for the letters. -/
theorem segment_profile_support_legs
    {L D N G W I : Type*} [AddCommGroup L] [Module ℝ L]
    [Group D] [Group N] [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ExpD : L → D) (hzero : ExpD 0 = 1) (ι : N →* G) (κ : D →* G)
    (J : G → W) (x d₀ : G) (center : W) (A : Set N) (r T ε : ℝ)
    (hT : 0 ≤ T) (v : L) (θ : I → ℝ) (hθ : ∀ i, θ i ∈ Icc 0 T)
    (g : ℝ → W)
    (hgood : ∀ u ∈ A, ∀ t ∈ Icc (0 : ℝ) T,
      ‖J ((x * ι u * d₀) * κ (ExpD ((r * t) • v))) - center - r • g t‖ ≤ ε) :
    (∀ u ∈ A, ‖J (x * ι u * d₀) - center - r • g 0‖ ≤ ε) ∧
    ∀ u ∈ A, ∀ i, ∀ t : unitInterval,
      ∃ w ∈ g '' Icc (0 : ℝ) T,
        ‖J ((x * ι u * d₀) * κ (ExpD ((r * t) • (θ i • v)))) - center - r • w‖ ≤ ε := by
  constructor
  · intro u hu
    simpa only [mul_zero, zero_smul, hzero, map_one, mul_one] using
      hgood u hu 0 ⟨le_rfl, hT⟩
  · intro u hu i t
    have ht : θ i * (t : ℝ) ∈ Icc (0 : ℝ) T := by
      refine ⟨mul_nonneg (hθ i).1 t.property.1, ?_⟩
      exact (mul_le_of_le_one_right (hθ i).1 t.property.2).trans (hθ i).2
    refine ⟨g (θ i * t), ⟨θ i * t, ht, rfl⟩, ?_⟩
    have he : (r * (t : ℝ)) • (θ i • v) = (r * (θ i * (t : ℝ))) • v := by
      rw [smul_smul]
      congr 1
      ring
    rw [he]
    exact hgood u hu _ ht

end PolycyclicRecognition

end

end OAI
