import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasedImagePaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceVolumeComparison

namespace OAI

/-! # Path-packing comparison along a sequence of profile scales -/

noncomputable section

namespace PolycyclicRecognition

open Filter Metric Set
open scoped NNReal ENNReal Topology Pointwise

variable {G W : Type*} [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ : ℝ≥0}

/-- Successful endpoint sets may lose subexponential mass. Center every
image path at its actual start before applying the ambient packing theorem. -/
theorem exponent_le_of_sequence_image_paths
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (π : G →* Multiplicative W) (E : Set W) (P : Set W → ℝ)
    {p K C D : ℝ} {Q : ℝ≥0∞} {mass : ℕ → ℝ}
    (hmass : HasSubexponentialLowerBoundSeq scale mass) (hΛ : 0 < (Λ : ℝ))
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hQ : Q < ⊤) (hD : 0 < D) (k : ℕ)
    (hlower : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      ∃ (f : NormalizedPair G Λ) (a : G) (s : Finset G),
        (∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) ∧
        ENNReal.ofReal (mass n) * ENNReal.ofReal (Real.exp (scale n * p)) ≤
          (s.card : ℝ≥0∞) * Q ∧
        ∀ g ∈ s, ∃ γ : Path a g,
          PathMetricBound γ (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
          ∀ t, ∃ z ∈ E,
            ‖(π (f.val.1 (γ t))).toAdd - (π (f.val.1 a)).toAdd - scale n • z‖ ≤
              η * scale n + K * Λ * C * (1 + Real.log (2 + scale n)))
    (hupper : ∀ {r L κ B ε : ℝ}, 0 < r → 0 ≤ L → 0 ≤ κ → 0 ≤ ε →
      K * (κ + 2) + B ≤ r * ε → ∀ s : Finset G,
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ dist x y) →
      (∀ x ∈ s, ∃ γ : Path (1 : G) x, PathMetricBound γ L κ ∧
        ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - r • z‖ ≤ B) →
      (s.card : ℝ) ≤ D * (3 + (L + 1) * (κ + 2)) ^ k *
        Real.exp (r * P (E + closedBall 0 ε))) :
    ∀ ε : ℝ, 0 < ε → p ≤ P (E + closedBall 0 ε) := by
  classical
  intro ε hε
  let A := (Λ : ℝ) * C
  let b := K * Λ * C
  have hA : 0 ≤ A := mul_nonneg Λ.coe_nonneg hC
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let H := 3 + (A + 1) * (3 * A + 2)
  have hH : 0 < H := by dsimp [H]; positivity
  apply exponent_le_of_sequence_separated_counts hscale hmass
    (show 0 < D * H ^ k by positivity) hQ (2 * k)
  filter_upwards [hlower η hη, hscale.eventually (eventually_ge_atTop (1 : ℝ)),
    hscale.eventually (eventually_logarithmic_error_le (2 * b) (2 * K) (half_pos hε))]
      with n hr hr1 hlog
  let r := scale n
  have hrpos : 0 < r := by linarith
  have hlog0 : 0 ≤ 1 + Real.log (2 + r) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2 + r)
    linarith
  obtain ⟨f, a, s, hsep, hlow, hpaths⟩ := hr
  let t := s.image (basedImage f.val.1 a)
  obtain ⟨hcard, hsep'⟩ := basedImage_separated_card f hΛ a s hsep
  let L := A * r
  let κ := A * (1 + Real.log (2 + r))
  let B := η * r + b * (1 + Real.log (2 + r))
  have hL : 0 ≤ L := mul_nonneg hA hrpos.le
  have hκ : 0 ≤ κ := mul_nonneg hA hlog0
  have herr : K * (κ + 2) + B ≤ r * ε := by
    dsimp only [κ, B, A, b, η] at *
    nlinarith
  have himage : ∀ x ∈ t, ∃ γ : Path (1 : G) x, PathMetricBound γ L κ ∧
      ∀ u, ∃ z ∈ E, ‖(π (γ u)).toAdd - r • z‖ ≤ B := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨γ, hγ, hh⟩ := hpaths g hg
    obtain ⟨ζ, hζ, hmetric⟩ := basedImage_map_path f.val.1 f.property.1.1 γ hγ
    refine ⟨ζ, ?_, ?_⟩
    · convert hmetric using 1 <;> dsimp [L, κ, A] <;> ring
    · intro u
      rw [hζ, basedImage_height]
      exact hh u
  have hcount := hupper hrpos hL hκ hε.le herr t hsep' himage
  refine ⟨s.card, hlow, ?_⟩
  rw [← hcard]
  apply hcount.trans
  have hpoly := coarse_path_word_prefactor_le hA hr1
  dsimp only [L, κ] at *
  calc
    _ ≤ D * (H * (1 + r) ^ 2) ^ k * Real.exp (r * P (E + closedBall 0 ε)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact pow_le_pow_left₀ (by positivity) hpoly k
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end PolycyclicRecognition

end

end OAI
