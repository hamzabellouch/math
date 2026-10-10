import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedPairPacking
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PairHeightCocycle
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePackingAsymptotics

namespace OAI

/-! # Stationary path-volume comparison

A common pair on a positive-volume endpoint set gives the lower exponential
count. Coarse path packing bounds its image count. Polynomial and logarithmic
losses disappear before the template thickening tends to zero.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter Metric Set
open scoped NNReal ENNReal Topology Pointwise

variable {G W : Type*} [Group G] [MetricSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ : ℝ≥0}

/-- Exact comparison with every positive enlargement of the image template. -/
theorem exponent_le_of_stationary_path_counts
    (π : G →* Multiplicative W) (E : Set W) (P : Set W → ℝ)
    {p K C D : ℝ} {a Q : ℝ≥0∞} (hΛ : 0 < (Λ : ℝ))
    (hK : 0 ≤ K) (hC : 0 ≤ C) (ha : 0 < a) (hafin : a < ⊤)
    (hQ : Q < ⊤) (hD : 0 < D) (k : ℕ)
    (hlower : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∃ r₀ : ℝ, 1 ≤ r₀ ∧
      ∀ r : ℝ, r₀ ≤ r → ∃ (f : NormalizedPair G Λ) (s : Finset G),
        (∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) ∧
        a * ENNReal.ofReal (Real.exp (r * p)) ≤ (s.card : ℝ≥0∞) * Q ∧
        ∀ g ∈ s, ∃ γ : Path (1 : G) g,
          PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
          ∀ t, ∃ z ∈ E, ‖pairHeight π (γ t) f - r • z‖ ≤
            (K * Λ * C * δ + η) * r + K * Λ * C * (1 + Real.log (2 + r)))
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
  let δ := ε / (4 * (b + 1))
  let η := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hcoef : b * δ + η ≤ ε / 2 := by
    have h : b * δ ≤ ε / 4 := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (b + 1))).mpr
      nlinarith
    dsimp [η]
    linarith
  obtain ⟨r₀, hr₀, hgood⟩ := hlower δ hδ η hη
  let F := 3 + (A + 1) * (3 * A + 2)
  have hF : 0 < F := by dsimp [F]; positivity
  apply exponent_le_of_separated_mass_bounds ha hafin
    (show 0 < D * F ^ k by positivity) hQ (2 * k)
  filter_upwards [eventually_ge_atTop r₀,
    eventually_logarithmic_error_le (2 * b) (2 * K) (half_pos hε)] with r hr hlog
  have hr1 : 1 ≤ r := hr₀.trans hr
  have hrpos : 0 < r := by linarith
  have hlog0 : 0 ≤ 1 + Real.log (2 + r) := by
    have hh := Real.log_nonneg (by linarith : 1 ≤ 2 + r)
    linarith
  obtain ⟨f, s, hsep, hlow, hpaths⟩ := hgood r hr
  let t := s.image f.val.1
  have hcard : t.card = s.card := normalizedPair_card_image f hΛ s hsep
  have hsep' : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → 1 ≤ dist x y :=
    normalizedPair_image_separated f hΛ s hsep
  let L := A * r
  let κ := A * (1 + Real.log (2 + r))
  let B := (b * δ + η) * r + b * (1 + Real.log (2 + r))
  have hL : 0 ≤ L := mul_nonneg hA hrpos.le
  have hκ : 0 ≤ κ := mul_nonneg hA hlog0
  have herr : K * (κ + 2) + B ≤ r * ε := by
    have hlin := mul_le_mul_of_nonneg_right hcoef hrpos.le
    dsimp only [κ, B, A, b] at *
    nlinarith
  have himage : ∀ x ∈ t, ∃ γ : Path (1 : G) x, PathMetricBound γ L κ ∧
      ∀ u, ∃ z ∈ E, ‖(π (γ u)).toAdd - r • z‖ ≤ B := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨γ, hγ, hh⟩ := hpaths g hg
    obtain ⟨ζ, hζ, hmetric⟩ := normalizedPair_map_path f γ hγ
    refine ⟨ζ, ?_, ?_⟩
    · convert hmetric using 1 <;> dsimp [L, κ, A] <;> ring
    · intro u
      rw [hζ]
      exact hh u
  have hcount := hupper hrpos hL hκ hε.le herr t hsep' himage
  refine ⟨s.card, hlow, ?_⟩
  rw [← hcard]
  apply hcount.trans
  have hpoly := coarse_path_word_prefactor_le hA hr1
  dsimp only [L, κ] at *
  calc
    _ ≤ D * (F * (1 + r) ^ 2) ^ k * Real.exp (r * P (E + closedBall 0 ε)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact pow_le_pow_left₀ (by positivity) hpoly k
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end PolycyclicRecognition

end

end OAI
