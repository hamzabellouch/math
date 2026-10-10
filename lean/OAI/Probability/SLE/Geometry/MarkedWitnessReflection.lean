import OAI.Probability.SLE.Gauge.SerpentineMarkedReflection
import OAI.Probability.SLE.BrownianStrongMarkov

namespace OAI

/-! The actual capacity witness and marked sine angle transform exactly
under reflection; no law comparison is needed for the geometric angle bound. -/

noncomputable section
open Set Metric
open scoped Topology NNReal

namespace SLEExactGauge.Serpentine

lemma mirrored_centered_value (z : ℂ) (u : ℝ) :
    loewnerMirror z - ((-u : ℝ) : ℂ) = loewnerMirror (z - (u : ℂ)) := by
  apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]

lemma mirrored_centered_sine (z : ℂ) (u : ℝ) :
    (loewnerMirror z - ((-u : ℝ) : ℂ)).im / ‖loewnerMirror z - ((-u : ℝ) : ℂ)‖ =
      (z - (u : ℂ)).im / ‖z - (u : ℂ)‖ := by
  rw [mirrored_centered_value, loewnerMirror_im, loewnerMirror_norm]

lemma mirrored_marked_sine (G : ℝ≥0 → ℂ → ℂ) (U : ℝ≥0 → ℝ) (T : ℝ≥0) (w : ℂ) :
    (loewnerMirror (G T (loewnerMirror (loewnerMirror w))) - ((-U T : ℝ) : ℂ)).im /
      ‖loewnerMirror (G T (loewnerMirror (loewnerMirror w))) - ((-U T : ℝ) : ℂ)‖ =
      (G T w - (U T : ℂ)).im / ‖G T w - (U T : ℂ)‖ := by
  rw [loewnerMirror_twice, mirrored_centered_sine]

lemma mirrored_front_freshness (γ : ℝ≥0 → ℂ) (T : ℝ≥0)
    (hfresh : ∀ S : ℝ≥0, S < T → γ T ∈ survivingDomain γ S) :
    ∀ S : ℝ≥0, S < T → (loewnerMirror ∘ γ) T ∈ survivingDomain (loewnerMirror ∘ γ) S := by
  intro S hS
  exact (loewnerMirror_surviving γ S (γ T)).mpr (hfresh S hS)

lemma mirrored_ball_surviving_iff (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (w : ℂ) (r : ℝ) :
    ball (loewnerMirror w) r ⊆ survivingDomain (loewnerMirror ∘ γ) T ↔
      ball w r ⊆ survivingDomain γ T := by
  constructor
  · intro h z hz
    exact (loewnerMirror_surviving γ T z).mp
      (h (by simpa only [mem_ball, loewnerMirror_dist] using hz))
  · intro h z hz
    have hz' : loewnerMirror z ∈ ball w r := by
      change dist (loewnerMirror z) w < r
      have hd := loewnerMirror_dist z (loewnerMirror w)
      rw [loewnerMirror_twice] at hd
      exact hd.trans_lt hz
    have hh := (loewnerMirror_surviving γ T (loewnerMirror z)).mpr (h hz')
    simpa only [loewnerMirror_twice] using hh

/-- Every item required by the marked-angle application is reflected
with the same capacity time and the negated continuous driver. -/
theorem marked_witness_reflection
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hfresh : ∀ S : ℝ≥0, S < T → γ T ∈ survivingDomain γ S) (w : ℂ) :
    IsCapacityTwoWitness (fun t => -U t) (loewnerMirror ∘ γ)
      (fun t z => loewnerMirror (G t (loewnerMirror z)))
      (fun t z => loewnerMirror (F t (loewnerMirror z))) ∧
    Continuous (fun t => -U t) ∧
    (∀ S : ℝ≥0, S < T → (loewnerMirror ∘ γ) T ∈ survivingDomain (loewnerMirror ∘ γ) S) ∧
    (loewnerMirror (G T (loewnerMirror (loewnerMirror w))) - ((-U T : ℝ) : ℂ)).im /
      ‖loewnerMirror (G T (loewnerMirror (loewnerMirror w))) - ((-U T : ℝ) : ℂ)‖ =
      (G T w - (U T : ℂ)).im / ‖G T w - (U T : ℂ)‖ :=
  ⟨hw.mirror, hU.neg, mirrored_front_freshness γ T hfresh, mirrored_marked_sine G U T w⟩

end SLEExactGauge.Serpentine

end

end OAI
