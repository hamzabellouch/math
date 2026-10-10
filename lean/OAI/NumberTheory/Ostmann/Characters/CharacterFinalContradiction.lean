import OAI.NumberTheory.Ostmann.Characters.CharacterNonanchorDecay
import OAI.NumberTheory.Ostmann.Construction.SelectedNaturalFinalContradiction

namespace OAI

/-! # The final comparison at the literal signed character prior -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_character_final_contradiction (n N : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x)
    (K B B₁ z c Cmass α βg βw γs νw ε : ℝ)
    (hB : 1 ≤ B) (hB₁ : 0 ≤ B₁) (hz : 1 ≤ z) (hc : 1 ≤ c)
    (hCmass : 0 < Cmass) (hα : 0 < α) (hβg : 0 < βg)
    (hαw : α < βw) (hsw : γs < βw) (hβw : βw < νw) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, M₀ ≤ (m : ℝ) →
      L ≤ m → (m : ℝ) ≤ z * L →
      ∀ (r : Fin (n + 1) → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
      (∀ j, r j ≤ N) → f ≤ N →
      ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : (Σ v, Fin (characterSize m r f v)) → Finset ℕ),
      (∀ i, Q i ⊆ P) →
      (∀ i, Real.exp (-Cmass * L) ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
      (∀ j p, p ∈ Q (characterAnchor m r f j false) →
        (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
      (∀ i p, p ∈ Q (characterBulk m r f i) → Real.exp (Real.exp (νw * L)) ≤ p) →
      (∀ i : Fin m, 1 ≤ ∑ p ∈ Q (characterBulk m r f i), (p : ℝ)⁻¹) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (J : ℕ) (lower upper : CharacterCell (n + 1) → ℕ) (logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let lo := initialWordAtomLower J lower
      let hi := initialWordAtomUpper J upper
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let V := naturalTransferCutoff Δ m
      ∀ (cap : ℕ → ℕ) (center : ∀ p : ℕ, ZMod p),
      Real.exp (-B₁ * (2 ^ (n + 1) : ℝ) * m) ≤
        ‖scheduledConstituentAmplitude (characterRole (n + 1)) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP Q lo hi V cap
          (scheduleFourierLeaf (characterRole (n + 1)) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))) center (n + 1)‖ →
      False := by
  let d := B + 20 * Real.log z
  let C₀ := (Fintype.card (CharacterRole (n + 1)) : ℝ) * c
  let D := (2 : ℝ) ^ (n + 1) * d + 2 * (4 : ℝ) ^ (n + 1)
  let C := max D (d + 1)
  let C₁ := βg + Real.log ((Real.log 2)⁻¹ + 1)
  let H := Cmass + βg + α + Real.log ((Real.log 2)⁻¹ + 1) + 2
  let S := max 1 (max (SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)))
    (SchwartzMap.seminorm ℝ 0 1 (𝓕 ψ : 𝓢(ℝ, ℂ))))
  have hz0 : 0 < z := by linarith
  have hd1 : 1 ≤ d := by dsimp [d]; linarith [Real.log_nonneg hz]
  have hd : 0 ≤ d := by linarith
  have hC : 0 ≤ C := (by dsimp [D]; positivity : (0 : ℝ) ≤ D).trans (le_max_left _ _)
  have hlc : 0 ≤ Real.log ((Real.log 2)⁻¹ + 1) := by
    have hh : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_pos (by norm_num)).le
    exact Real.log_nonneg (by linarith)
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; linarith
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hHm : Cmass ≤ H := by dsimp [H]; linarith
  have hHdy : βg + Real.log ((Real.log 2)⁻¹ + 1) ≤ H := by dsimp [H]; linarith
  have hHratio : βg - α ≤ H := by dsimp [H]; linarith
  obtain ⟨M₁, hcontra⟩ := selected_natural_final_contradiction (characterRole (n + 1)) n 1
    (3 ^ (n + 1) * Fintype.card (CharacterRole (n + 1))) ((N : ℝ) + 2) C S H z
    α βw γs 1 (by positivity) hC (le_max_left _ _) hH hz0.le hα hαw hsw (by norm_num)
    ψ hreal C₀ K d ε hd hε B₁ (C₁ + max (Real.log 3) 0 + ε) hB₁
    (by exact hentropy) hψ
  refine ⟨max M₁ (max 1 C₀), ?_⟩
  filter_upwards [hcontra,
    eventual_character_band_lower βw νw (hα.trans (hαw.trans hβw)) hβw,
    eventual_natural_cutoff_below_primes (n + 1) d z α 1 hd hz0.le hα (by norm_num),
    eventual_character_energy_prime_range (n + 1) ((2 ^ (n + 2) - 1) * (n + 3))
      d z α βg hd hz0.le hα hβg.le,
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hβg)).eventually
      (eventually_ge_atTop (2 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with L hcontra hAw hlarge hdyadic hRthree hL
  intro m hM hLM hmL r f hr hrN hf P hP Q hQP hmass hPrange hsmall hword hbulk
    χ hχ J lower upper logX hlogX Δ lo hi χ₀ V cap center hamp
  have hm : (1 : ℝ) ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hM₁ : M₁ ≤ (m : ℝ) := (le_max_left _ _).trans hM
  have hCm : C₀ ≤ (m : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hms : 0 < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  let i : Fin m := ⟨0, hms⟩
  have hpos (i) : 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹ := (Real.exp_pos _).trans_le (hmass i)
  have hPne : P.Nonempty := by
    have hne : Q (characterTop m r f) ≠ ∅ := by
      intro he
      have hh := hpos (characterTop m r f)
      simp only [he, Finset.sum_empty, lt_self_iff_false] at hh
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact ⟨q, hQP _ hq⟩
  let A := ⌈Real.exp (Real.exp (βw * L))⌉₊
  let E := ⌊Real.exp (Real.exp (βg * L))⌋₊
  let Bq := ⌊Real.exp (Real.exp (γs * L))⌋₊
  let ℓ := Real.exp (Real.exp (α * L))
  let Rmax := Real.exp (Real.exp (βg * L))
  have hE : (E : ℝ) ≤ Rmax := Nat.floor_le (Real.exp_nonneg _)
  have hWB := character_initial_window_bounds d C₀ m hd1 hm (by dsimp [C₀]; positivity) hCm
  change 1 ≤ Real.exp (Δ - C₀) ∧ Real.exp (Δ - C₀) ≤ Real.exp (Δ + C₀) ∧
    Real.exp (Δ + C₀) - Real.exp (Δ - C₀) ≤ Real.exp ((d + 1) * m) at hWB
  have hXlo : 1 < Real.exp logX * Real.exp (Δ - C₀) := by
    have he := Real.one_lt_exp_iff.mpr hlogX
    have hlo := hWB.1
    nlinarith only [he, hlo]
  have huniq : ∀ j < n + 1, ∀ u v, characterRole (n + 1) u = .pivot j →
      characterRole (n + 1) v = .pivot j → u = v := by
    intro j hj u v hu hv
    exact (characterPivotAtom_unique ⟨j, hj⟩ u hu).trans (characterPivotAtom_unique ⟨j, hj⟩ v hv).symm
  have hcounts := character_interval_complexity (n + 1) (n + 1) le_rfl lo hi
  have hfreq : (V (n + 1) : ℝ) ≤ Real.exp (C * (m : ℝ)) := by
    apply (naturalTransferCutoff_linear_bound (n + 1) (n + 1) d m le_rfl hd hm).trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  have hwidth : ∀ j, (WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ))
      (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) hWB.1 hWB.2.1).upper j -
      (WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ))
      (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) hWB.1 hWB.2.1).lower j ≤
        Real.exp (C * (1 + (m : ℝ))) := by
    intro j
    apply hWB.2.2.trans
    apply Real.exp_le_exp.mpr
    have hdC := le_max_right D (d + 1)
    nlinarith only [hdC, hC, Nat.cast_nonneg (α := ℝ) m]
  obtain ⟨h, JJ, hmod, hrange, hJJ⟩ := hdyadic (m : ℝ) hm hmL (Q (characterBulk m r f i))
    (fun q hq => hPrange q (hQP _ hq))
  exact hcontra (characterSize m r f) (m + N + 1) (by omega)
    (characterSize_le (n + 1) m N r f hrN hf) m hM₁ (Nat.cast_nonneg _) hmL
    (characterSize_linear_bound m N) χ₀ (fun i => primeGaussMultiplier (χ₀ i))
    (fun i p => (primeGaussMultiplier_norm _ _).le) (characterPivot m r f hr) V cap
    (atomIntervalRanges (characterRole (n + 1)) lo hi) hcounts.1 hcounts.2
    (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) hWB.1 hWB.2.1
    (Real.exp_pos _) hXlo huniq m (characterBulk m r f) (characterBulk_role m r f)
    (fun j => characterAnchor m r f j false) (fun j => rfl)
    (fun j hj => characterPivot_role m r f hr j hj) P hPne hP Q hQP hpos
    A E Bq hAw.1 ℓ (Real.exp (α * L)) Rmax (Real.exp_pos _) (Real.exp_pos _)
    (by
      have hh : 2 ≤ Real.exp (βg * L) := by simpa only [Function.comp_apply, id_eq] using hRthree
      have he := Real.add_one_le_exp (Real.exp (βg * L))
      linarith)
    (fun j q hq => hχ q (hQP _ hq))
    (fun j q hq => ⟨(hPrange q (hQP _ hq)).1, Nat.le_floor (hsmall j q hq)⟩)
    (fun j q hq => ⟨hAw.2.2 q (hword j q hq), Nat.le_floor (hPrange q (hQP _ hq)).2⟩)
    (fun q hq => (Real.le_log_iff_exp_le (by exact_mod_cast (hP q hq).pos)).mpr (hPrange q hq).1)
    (fun q hq => (hPrange q hq).2) hfreq
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _)) hwidth
    (character_prime_band_dyadic_budget E βg L m H hβg.le hL hLM hHdy hH hE)
    (fun i => (harmonic_mass_inv_energy_budget (Q i) Cmass L m hCmass.le hLM (hmass i)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hHm (by linarith))))
    (by simp only [one_mul]; exact le_rfl) hAw.2.1 (Nat.floor_le (Real.exp_nonneg _))
    (fun q hq => by simpa only [one_mul] using (hPrange q hq).1)
    (character_prime_band_log_ratio α βg L m H (by linarith) hLM hβg.le hHratio hH)
    (fun q hq => hlarge _ hm hmL q (by simpa only [one_mul] using (hPrange q hq).1) _ le_rfl)
    (characterBulk m r f i) rfl le_rfl h JJ (hmod (n + 1) le_rfl) hrange
    1 C₁ (by norm_num) hL (hbulk i) hJJ center rfl hLM hC₁
    (by simp only [div_one]; exact le_rfl) hamp

end Ostmann

end OAI
