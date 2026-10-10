import OAI.MathematicalPhysics.Boltzmann.Branching.PerturbedFiniteBlock
import OAI.MathematicalPhysics.Boltzmann.Jets.BeamNormalOutgoing

namespace OAI

/-! # Uniform branching growth from coefficient bounds only on the visited cylinder -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem uniform_local_beam_block {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∃ N : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ y : ℝ × V, y.1 ∈ Icc (endTime-A) endTime → ‖y.2-z.1‖ ≤ 6*A → BeamNear b ε y) →
      (6 : ℝ≥0∞) < mediumBlockMass b endTime T (A,z) κ d N := by
  obtain ⟨A₀,hA₀,hgrowth⟩ := uniform_perturbed_block_growth hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT
  obtain ⟨N,ε₁,hε₁,hblock⟩ := hgrowth T hT
  let L : ℝ := (N:ℝ)+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨N,min ε₁ (1/L),lt_min hε₁ (one_div_pos.mpr hL),?_⟩
  intro ε hε A hA z b endTime hnear
  apply hblock ε ⟨hε.1,hε.2.trans (min_le_left _ _)⟩ A hA z b endTime
  intro n hn a ha
  have hnL : (n:ℝ) ≤ L := (Nat.cast_le.mpr hn.le).trans (le_add_of_nonneg_right (by norm_num))
  have hbudget : (n:ℝ)*ε ≤ 1 :=
    (mul_le_mul_of_nonneg_right hnL hε.1).trans (by
      have hh := (le_div_iff₀ hL).mp (hε.2.trans (min_le_right _ _))
      simpa only [mul_comm] using hh)
  exact wordNearby_from_start b endTime A z hε.1 (hA₀.le.trans hA.1) hnear n hbudget a ha

theorem uniform_physical_beam_block {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∃ N : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc A₀ T, ∀ v : RetainedState,
      ∀ (b : BeamCoefficients) (ρ t₀ : ℝ) (x₀ : V), 0 < ρ →
      (∀ p : ℝ × V, p.1 ∈ Icc t₀ (t₀+A/ρ) → ‖p.2-x₀‖ ≤ 6*A/ρ → BeamNear b ε p) →
      (6 : ℝ≥0∞) < mediumBlockMass (b.normalized ρ t₀ x₀) A T (A,(0,v)) κ d N := by
  obtain ⟨A₀,hA₀,hgrowth⟩ := uniform_local_beam_block hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT
  obtain ⟨N,ε₀,hε₀,hblock⟩ := hgrowth T hT
  refine ⟨N,ε₀,hε₀,?_⟩
  intro ε hε A hA v b ρ t₀ x₀ hρ hnear
  apply hblock ε hε A hA (0,v) (b.normalized ρ t₀ x₀) A
  intro p hp hx
  exact normalized_beam_near b hρ x₀ hnear p (by simpa using hp) (by simpa using hx)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
