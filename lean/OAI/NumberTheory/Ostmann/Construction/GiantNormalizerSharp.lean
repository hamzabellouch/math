import OAI.NumberTheory.Ostmann.Construction.SmoothLogCellProfile

namespace OAI

/-! # The Section 7 bound on the actual giant normalizer -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem PublishedProgressionInput.giant_normalizer_sharp (P : PublishedProgressionInput) :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℝ,
      2 ≤ G → Real.exp ((39 / 10000 : ℝ) * L) ≤ G - 1 / 2 →
      G ≤ Real.exp ((905 / 1000 : ℝ) * L) →
      Real.exp (-(91 / 100 : ℝ) * L) ≤
        smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
      smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤
        (91 / 100 : ℝ) * L := by
  have ht : Tendsto (fun L : ℝ => Real.exp ((1 / 200 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [P.short_cell_mass_error_relative (905 / 1000),
    ht.eventually (eventually_ge_atTop (4 / logCellCentralLower)),
    eventually_ge_atTop (4000 : ℝ)] with L herrate hsmall hL
  intro G hG hlo hhi
  have hlog : Real.log (4 * (2 : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 * 2)
    have h2 := Real.add_one_le_exp ((12 / 10000 : ℝ) * L)
    norm_num at h1 ⊢
    nlinarith
  have hcard : (Fintype.card Unit : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) := by
    simpa only [Fintype.card_unique, Nat.cast_one] using
      (Real.one_le_exp (Real.exp_nonneg ((14 / 10000 : ℝ) * L)))
  have herr := herrate Unit 2 (by omega) hlog hcard (fun _ => G - 1 / 2) (fun _ => hlo)
  simp only [Fintype.sum_unique] at herr
  have hinv : Real.exp (-(905 / 1000 : ℝ) * L) ≤ G⁻¹ := by
    rw [neg_mul, Real.exp_neg]
    exact inv_anti₀ (by linarith : 0 < G) hhi
  have herr' : bulkPrimeErrorFactor P 2 (G - 1 / 2) ≤ (4 * G)⁻¹ := by
    apply herr.trans
    calc
      Real.exp (-(905 / 1000 : ℝ) * L) / 4 ≤ G⁻¹ / 4 :=
        div_le_div_of_nonneg_right hinv (by norm_num)
      _ = _ := by ring
  have hm := P.smoothGiantMass_lower logCellProfile G logCellCentralLower hG
    logCellCentralLower_pos logCellProfile_nonneg logCellProfile_central herr'
  have hb : Real.exp (-(1 / 200 : ℝ) * L) ≤ logCellCentralLower / 4 := by
    have hi := inv_anti₀ (div_pos (by norm_num) logCellCentralLower_pos) hsmall
    simpa only [neg_mul, Real.exp_neg, one_div, inv_div, inv_inv] using hi
  have hmass : Real.exp (-(91 / 100 : ℝ) * L) ≤
      smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G := by
    apply le_trans _ hm
    calc
      Real.exp (-(91 / 100 : ℝ) * L) =
          Real.exp (-(1 / 200 : ℝ) * L) * Real.exp (-(905 / 1000 : ℝ) * L) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (logCellCentralLower / 4) * G⁻¹ :=
        mul_le_mul hb hinv (Real.exp_nonneg _) (div_nonneg logCellCentralLower_pos.le (by norm_num))
      _ = _ := by ring
  refine ⟨hmass, ?_⟩
  have hlogmass := Real.log_le_log (Real.exp_pos _) hmass
  rw [Real.log_exp] at hlogmass
  change -Real.log (smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G) ≤ _
  linarith

end Ostmann

end OAI
