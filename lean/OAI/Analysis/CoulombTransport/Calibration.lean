import OAI.Analysis.CoulombTransport.Model

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A bounded-below signed potential is made nonnegative by a constant shift. -/
def shiftedPotential (u : E3 → ℝ) (M : ℝ) (x : E3) : ℝ≥0∞ :=
  ENNReal.ofReal (u x + M)

lemma measurable_shiftedPotential {u : E3 → ℝ} (hu : Measurable u) (M : ℝ) :
    Measurable (shiftedPotential u M) :=
  (hu.add_const M).ennreal_ofReal

lemma shifted_three_sum {a b c M : ℝ}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) :
    ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) =
      ENNReal.ofReal (a + b + c + 3 * M) := by
  have ha' : 0 ≤ a + M := by linarith
  have hb' : 0 ≤ b + M := by linarith
  have hc' : 0 ≤ c + M := by linarith
  rw [← ENNReal.ofReal_add ha' hb', ← ENNReal.ofReal_add (add_nonneg ha' hb') hc']
  congr 1
  ring

lemma shifted_three_le {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c)
    (h : ENNReal.ofReal (a + b + c) ≤ z) :
    ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) ≤
      z + ENNReal.ofReal (3 * M) := by
  rw [shifted_three_sum ha hb hc]
  exact ENNReal.ofReal_add_le.trans (add_le_add h le_rfl)

lemma shifted_three_eq_of_contact {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M)
    (hs : 0 ≤ a + b + c) (hz : ENNReal.ofReal (a + b + c) = z) :
    ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) =
      z + ENNReal.ofReal (3 * M) := by
  rw [shifted_three_sum ha hb hc, ENNReal.ofReal_add hs (by positivity), hz]

lemma contact_of_shifted_three_eq {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M)
    (h : ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) +
      ENNReal.ofReal (c + M) = z + ENNReal.ofReal (3 * M)) :
    0 ≤ a + b + c ∧ ENNReal.ofReal (a + b + c) = z := by
  rw [shifted_three_sum ha hb hc] at h
  have hz : z ≠ ⊤ := by
    intro hz
    simp only [hz, top_add] at h
    exact ENNReal.ofReal_ne_top h
  have hs : 0 ≤ a + b + c + 3 * M := by linarith
  have ht := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal hs, ENNReal.toReal_add hz ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 3 * M)] at ht
  have heq : a + b + c = z.toReal := by linarith
  constructor
  · rw [heq]
    exact ENNReal.toReal_nonneg
  · rw [heq, ENNReal.ofReal_toReal hz]

lemma shifted_three_eq_iff {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M) :
    (ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) =
      z + ENNReal.ofReal (3 * M)) ↔
      0 ≤ a + b + c ∧ ENNReal.ofReal (a + b + c) = z := by
  exact ⟨contact_of_shifted_three_eq ha hb hc hM,
    fun h => shifted_three_eq_of_contact ha hb hc hM h.1 h.2⟩

/-- The shift preserves the supporting inequality, including negative signed sums. -/
lemma shifted_three_le_iff {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M) :
    (ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) ≤
      z + ENNReal.ofReal (3 * M)) ↔ ENNReal.ofReal (a + b + c) ≤ z := by
  constructor
  · intro h
    by_cases hs : 0 ≤ a + b + c
    · rw [shifted_three_sum ha hb hc, ENNReal.ofReal_add hs (by positivity)] at h
      exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h
    · rw [ENNReal.ofReal_of_nonpos (le_of_not_ge hs)]
      exact bot_le
  · exact shifted_three_le ha hb hc

/-- For a positive cost, equality already forces nonnegativity of the signed sum. -/
lemma shifted_three_eq_iff_of_pos {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M)
    (hz : 0 < z) :
    (ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) =
      z + ENNReal.ofReal (3 * M)) ↔ ENNReal.ofReal (a + b + c) = z := by
  rw [shifted_three_eq_iff ha hb hc hM]
  constructor
  · exact And.right
  · intro h
    refine ⟨le_of_lt (ENNReal.ofReal_pos.mp ?_), h⟩
    rw [h]
    exact hz

lemma shiftedPotential_certificate {u : E3 → ℝ} {M : ℝ} {t : Triple}
    (h1 : -M ≤ u (tripleFst t)) (h2 : -M ≤ u (tripleSnd t))
    (h3 : -M ≤ u (tripleThd t))
    (h : ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
      coulombCost t) :
    shiftedPotential u M (tripleFst t) + shiftedPotential u M (tripleSnd t) +
      shiftedPotential u M (tripleThd t) ≤ coulombCost t + ENNReal.ofReal (3 * M) :=
  shifted_three_le h1 h2 h3 h

lemma shiftedPotential_contact_iff {u : E3 → ℝ} {M : ℝ} {t : Triple}
    (h1 : -M ≤ u (tripleFst t)) (h2 : -M ≤ u (tripleSnd t))
    (h3 : -M ≤ u (tripleThd t)) (hM : 0 ≤ M) :
    (shiftedPotential u M (tripleFst t) + shiftedPotential u M (tripleSnd t) +
      shiftedPotential u M (tripleThd t) = coulombCost t + ENNReal.ofReal (3 * M)) ↔
      0 ≤ u (tripleFst t) + u (tripleSnd t) + u (tripleThd t) ∧
      ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) =
        coulombCost t :=
  shifted_three_eq_iff h1 h2 h3 hM

/-- An almost-everywhere upper bound suffices for finiteness of the shifted
potential; no signed-integrability conversion is needed. -/
lemma lintegral_shiftedPotential_le_of_ae_le {mu : Measure E3} [IsProbabilityMeasure mu]
    {u : E3 → ℝ} {M A : ℝ} (hbound : ∀ᵐ x ∂mu, u x ≤ A) :
    (∫⁻ x, shiftedPotential u M x ∂mu) ≤ ENNReal.ofReal (A + M) := by
  calc
    (∫⁻ x, shiftedPotential u M x ∂mu) ≤ (∫⁻ _x, ENNReal.ofReal (A + M) ∂mu) := by
      apply lintegral_mono_ae
      exact hbound.mono fun x hx => ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (A + M) := by simp

lemma lintegral_shiftedPotential_lt_top_of_ae_le {mu : Measure E3}
    [IsProbabilityMeasure mu] {u : E3 → ℝ} {M A : ℝ}
    (hbound : ∀ᵐ x ∂mu, u x ≤ A) :
    (∫⁻ x, shiftedPotential u M x ∂mu) < ⊤ :=
  (lintegral_shiftedPotential_le_of_ae_le hbound).trans_lt ENNReal.ofReal_lt_top

lemma lintegral_shiftedPotential {mu : Measure E3} [IsProbabilityMeasure mu]
    {u : E3 → ℝ} (hu : Integrable u mu) (M : ℝ)
    (hbound : ∀ᵐ x ∂mu, -M ≤ u x) :
    (∫⁻ x, shiftedPotential u M x ∂mu) =
      ENNReal.ofReal ((∫ x, u x ∂mu) + M) := by
  have hn : 0 ≤ᵐ[mu] fun x => u x + M := hbound.mono fun x hx => by
    dsimp
    linarith
  have hi : Integrable (fun x => u x + M) mu := hu.add (integrable_const M)
  calc
    (∫⁻ x, shiftedPotential u M x ∂mu) =
        ENNReal.ofReal (∫ x, u x + M ∂mu) :=
      (ofReal_integral_eq_lintegral_ofReal hi hn).symm
    _ = ENNReal.ofReal ((∫ x, u x ∂mu) + M) := by
      rw [integral_add hu (integrable_const M)]
      simp

lemma lintegral_shiftedPotential_lt_top {mu : Measure E3} [IsProbabilityMeasure mu]
    {u : E3 → ℝ} (hu : Integrable u mu) (M : ℝ)
    (hbound : ∀ᵐ x ∂mu, -M ≤ u x) :
    (∫⁻ x, shiftedPotential u M x ∂mu) < ⊤ := by
  rw [lintegral_shiftedPotential hu M hbound]
  exact ENNReal.ofReal_lt_top

end Problem356

end

end OAI
