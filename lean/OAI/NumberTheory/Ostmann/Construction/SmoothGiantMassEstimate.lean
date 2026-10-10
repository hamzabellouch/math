import OAI.NumberTheory.Ostmann.Construction.SmoothGiantSupport
import OAI.NumberTheory.Ostmann.Construction.PrimeCellMassRate

namespace OAI

/-! # The smooth giant normalizer from the published progression estimate -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators

private theorem central_harmonic_interval_lower (G : ℝ) (hG : 2 ≤ G) :
    (2 * G)⁻¹ ≤ ∫ x in Set.Ioc (G - 1 / 2) (G + 1 / 2), (x : ℝ)⁻¹ := by
  have hu : 0 < G - 1 / 2 := by linarith
  have hv : 0 < G + 1 / 2 := by linarith
  rw [harmonic_box_mass_log _ _ hu (by linarith)]
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hv hu)
  have he : 1 - ((G + 1 / 2) / (G - 1 / 2))⁻¹ = (G + 1 / 2)⁻¹ := by
    field_simp
    ring
  rw [he] at hh
  exact (inv_anti₀ hv (by linarith : G + 1 / 2 ≤ 2 * G)).trans hh

/-- A fixed positive part of the bump supplies a genuine lower bound for
its original prime mass; the only analytic input is the published progression
estimate at modulus one. -/
theorem PublishedProgressionInput.smoothGiantMass_lower
    (P : PublishedProgressionInput) (φ : ℝ → ℝ) (G b : ℝ)
    (hG : 2 ≤ G) (hb : 0 < b) (hφ : ∀ x, 0 ≤ φ x)
    (hcentral : ∀ x, |x| ≤ 1 / 2 → b ≤ φ x)
    (herr : bulkPrimeErrorFactor P 2 (G - 1 / 2) ≤ (4 * G)⁻¹) :
    b / (4 * G) ≤ smoothGiantMass (smoothGiantPrimeRange G) φ G := by
  let S := primeLogCellSet 1 0 (G - 1 / 2) (G + 1 / 2)
  have hSP : S ⊆ smoothGiantPrimeRange G := by
    intro p hp
    obtain ⟨hp, _, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hp.pos, ?_⟩, hp⟩
    have hlog : Real.log p ≤ G + 1 := by linarith
    have hp' : (p : ℝ) ≤ (⌈Real.exp (G + 1)⌉₊ : ℕ) :=
      ((Real.log_le_iff_le_exp (Nat.cast_pos.mpr hp.pos)).mp hlog).trans (Nat.le_ceil _)
    exact_mod_cast hp'
  have hmass := primeLogCell_page_mass_error P (Q := 2) (q := 1) (a := 0)
    (by omega) (by omega) (by omega) (by simp)
    (G - 1 / 2) (G + 1 / 2) (by linarith) (by linarith) (by linarith)
  rw [primeLogCellMeasure_mass, primeGiantMeasure_one_mass P 2 0 _ _ (by linarith)] at hmass
  have hlo : (4 * G)⁻¹ ≤ ∑ p ∈ S, (p : ℝ)⁻¹ := by
    have hi := central_harmonic_interval_lower G hG
    have he := (abs_le.mp (hmass.trans herr)).1
    have hpos : G ≠ 0 := by linarith
    have hid : (2 * G)⁻¹ = 2 * (4 * G)⁻¹ := by field_simp; ring
    rw [hid] at hi
    dsimp only [S]
    linarith
  have hlower := Ostmann.smoothGiantMass_lower (smoothGiantPrimeRange G) S hSP φ G b hφ
    (fun p hp => by
      obtain ⟨_, _, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp hp
      apply hcentral
      rw [abs_le]
      constructor <;> linarith)
  exact (show b / (4 * G) ≤ b * ∑ p ∈ S, (p : ℝ)⁻¹ by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hlo hb.le).trans hlower

/-- The loss of every admissible giant shell is linear in `L`, uniformly
in its center. This derives both positivity and normalization from the
published progression estimate, rather than assuming a prime in the shell. -/
theorem PublishedProgressionInput.smoothGiant_normalizer_rate
    (P : PublishedProgressionInput) (C b : ℝ) (hb : 0 < b)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (hcentral : ∀ x, |x| ≤ 1 / 2 → b ≤ φ x) :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℝ,
      2 ≤ G → Real.exp ((39 / 10000 : ℝ) * L) ≤ G - 1 / 2 →
      G ≤ Real.exp (C * L) →
      Real.exp (-(C + 1 / 10) * L) ≤ smoothGiantMass (smoothGiantPrimeRange G) φ G ∧
      smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G ≤ (C + 1 / 10) * L ∧
      (∑ p : smoothGiantPrimeRange G, smoothGiantPrior (smoothGiantPrimeRange G) φ G p) = 1 := by
  filter_upwards [P.short_cell_mass_error_relative C,
    eventually_ge_atTop (4000 : ℝ), eventually_ge_atTop (10 * Real.log (4 / b))]
    with L hrate hL hLb
  intro G hG hlo hhi
  have hlog : Real.log (4 * (2 : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 * 2)
    have h2 := Real.add_one_le_exp ((12 / 10000 : ℝ) * L)
    norm_num at h1 ⊢
    nlinarith
  have hcard : (Fintype.card Unit : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) := by
    simpa only [Fintype.card_unique, Nat.cast_one] using
      (Real.one_le_exp (Real.exp_nonneg ((14 / 10000 : ℝ) * L)))
  have herr := hrate Unit 2 (by omega) hlog hcard (fun _ => G - 1 / 2) (fun _ => hlo)
  simp only [Fintype.sum_unique] at herr
  have hinv : Real.exp (-C * L) ≤ G⁻¹ := by
    rw [neg_mul, Real.exp_neg]
    exact inv_anti₀ (by linarith : 0 < G) hhi
  have herr' : bulkPrimeErrorFactor P 2 (G - 1 / 2) ≤ (4 * G)⁻¹ := by
    apply herr.trans
    calc
      Real.exp (-C * L) / 4 ≤ G⁻¹ / 4 := div_le_div_of_nonneg_right hinv (by norm_num)
      _ = _ := by ring
  have hm := P.smoothGiantMass_lower φ G b hG hb hφ hcentral herr'
  have hb' : Real.exp (-(L / 10)) ≤ b / 4 := by
    calc
      Real.exp (-(L / 10)) ≤ Real.exp (-Real.log (4 / b)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = b / 4 := by
        rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num : (0 : ℝ) < 4) hb)]
        field_simp
  have hmass : Real.exp (-(C + 1 / 10) * L) ≤ smoothGiantMass (smoothGiantPrimeRange G) φ G := by
    apply le_trans _ hm
    calc
      Real.exp (-(C + 1 / 10) * L) = Real.exp (-(L / 10)) * Real.exp (-C * L) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (b / 4) * G⁻¹ := mul_le_mul hb' hinv (Real.exp_nonneg _) (by positivity)
      _ = b / (4 * G) := by ring
  have hmasspos := lt_of_lt_of_le (Real.exp_pos _) hmass
  refine ⟨hmass, ?_, smoothGiantPrior_mass _ φ G hmasspos⟩
  have hl := Real.log_le_log (Real.exp_pos _) hmass
  rw [Real.log_exp] at hl
  unfold smoothGiantLogNormalizer
  linarith

end Ostmann

end OAI
