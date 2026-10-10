import Mathlib

namespace OAI

/-!
# Accuracy assembly for the edit-distance approximation scheme

The probability and integer-conversion bounds of Section 8 of
*An Almost-Linear Approximation Scheme for Edit Distance*
(OpenAI, September 24, 2026) follow from the refinement estimate and
simultaneous seed guarantee using Markov's inequality.
-/

namespace EditApproximation

open MeasureTheory

/-- The implementation clamps to the input length and rounds down. -/
noncomputable def integerAnswer (N : ℕ) (value : ℝ) : ℕ :=
  ⌊max 0 (min (N : ℝ) value)⌋₊

/-- Clamping and rounding down preserve a one-sided approximation of an
integer distance.  This does not assert that an estimator has that bound. -/
theorem integerAnswer_spec {N D : ℕ} {value ε : ℝ}
    (hDN : D ≤ N) (hε : 0 ≤ ε)
    (hlower : (D : ℝ) ≤ value) (hupper : value ≤ (1 + ε) * D) :
    D ≤ integerAnswer N value ∧
      (integerAnswer N value : ℝ) ≤ (1 + ε) * D := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hmin : (D : ℝ) ≤ min (N : ℝ) value :=
    le_min (by exact_mod_cast hDN) hlower
  have hnonneg : 0 ≤ max 0 (min (N : ℝ) value) := le_max_left _ _
  constructor
  · exact (Nat.le_floor_iff hnonneg).2 (hmin.trans (le_max_right _ _))
  · apply (Nat.floor_le hnonneg).trans
    exact max_le (by positivity) ((min_le_right _ _).trans hupper)

@[simp] theorem integerAnswer_zero (N : ℕ) : integerAnswer N 0 = 0 := by
  simp [integerAnswer, Nat.cast_nonneg]

/-- The positive excess on executions having a good seed. -/
noncomputable def goodExcess {Ω : Type*} (G : Set Ω) (value : Ω → ℝ) (D : ℕ) :
    Ω → ℝ := G.indicator (fun ω => max (value ω - D) 0)

theorem goodExcess_nonneg {Ω : Type*} (G : Set Ω) (value : Ω → ℝ) (D : ℕ)
    (ω : Ω) : 0 ≤ goodExcess G value D ω := by
  classical
  by_cases hω : ω ∈ G <;> simp [goodExcess, hω]

/-- Markov's inequality converts the positive-excess expectation bound of
Section 8 into an approximation tail bound. -/
theorem goodExcess_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {G : Set Ω} {value : Ω → ℝ} {D : ℕ} {ℓ ε : ℝ}
    (hD : 0 < D) (hℓ : 0 < ℓ) (hε : 0 < ε)
    (hint : Integrable (goodExcess G value D) μ)
    (hmoment : (∫ ω, goodExcess G value D ω ∂μ) ≤ (D : ℝ) / ℓ) :
    μ.real {ω | ε * D ≤ goodExcess G value D ω} ≤ 1 / (ℓ * ε) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (goodExcess_nonneg G value D)) hint (ε * D)
  have htail : μ.real {ω | ε * D ≤ goodExcess G value D ω} ≤
      ((D : ℝ) / ℓ) / (ε * D) :=
    (le_div_iff₀ (mul_pos hε hDr)).2 (by
      simpa only [mul_comm] using hmarkov.trans hmoment)
  have hratio : ((D : ℝ) / ℓ) / (ε * D) = 1 / (ℓ * ε) := by
    field_simp
  rwa [hratio] at htail

/-- Final probability assembly, with the two genuinely unresolved
algorithmic guarantees exposed: a good-seed event and its excess moment.
The stronger success probability `4/5` implies the paper's `2/3`. -/
theorem final_answer_accuracy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Set Ω} {value : Ω → ℝ} {N D : ℕ} {ℓ ε : ℝ}
    (hvalue : Measurable value) (hDN : D ≤ N) (hD : 0 < D)
    (hℓ : 0 < ℓ) (hε : 0 < ε) (haccuracy : 10 ≤ ℓ * ε)
    (hseed : μ.real Gᶜ ≤ 1 / 10)
    (hlower : ∀ ω ∈ G, (D : ℝ) ≤ value ω)
    (hint : Integrable (goodExcess G value D) μ)
    (hmoment : (∫ ω, goodExcess G value D ω ∂μ) ≤ (D : ℝ) / ℓ) :
    (4 / 5 : ℝ) ≤ μ.real {ω | D ≤ integerAnswer N (value ω) ∧
      (integerAnswer N (value ω) : ℝ) ≤ (1 + ε) * D} := by
  classical
  let S : Set Ω := {ω | (D : ℝ) ≤ value ω ∧ value ω ≤ (1 + ε) * D}
  let B : Set Ω := {ω | ε * D ≤ goodExcess G value D ω}
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const hvalue).inter
      (measurableSet_le hvalue measurable_const)
  have hbad : Sᶜ ⊆ Gᶜ ∪ B := by
    intro ω hω
    by_cases hG : ω ∈ G
    · right
      have hupper : (1 + ε) * D < value ω := by
        by_contra hn
        exact hω ⟨hlower ω hG, le_of_not_gt hn⟩
      change ε * D ≤ goodExcess G value D ω
      simp only [goodExcess, Set.indicator_of_mem hG]
      apply le_trans _ (le_max_left _ _)
      nlinarith
    · exact Or.inl hG
  have htail : μ.real B ≤ 1 / (ℓ * ε) :=
    goodExcess_tail μ hD hℓ hε hint hmoment
  have hratio : 1 / (ℓ * ε) ≤ (1 / 10 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) haccuracy
  have hfail : μ.real Sᶜ ≤ (1 / 5 : ℝ) := calc
    μ.real Sᶜ ≤ μ.real (Gᶜ ∪ B) := measureReal_mono hbad
    _ ≤ μ.real Gᶜ + μ.real B := measureReal_union_le (μ := μ) _ _
    _ ≤ 1 / 5 := by linarith
  have hmass : μ.real S + μ.real Sᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := μ) hS
  have hsuccess : (4 / 5 : ℝ) ≤ μ.real S := by linarith
  apply hsuccess.trans
  exact measureReal_mono (μ := μ) (fun ω hω =>
    integerAnswer_spec hDN hε.le hω.1 hω.2)

end EditApproximation

end OAI
