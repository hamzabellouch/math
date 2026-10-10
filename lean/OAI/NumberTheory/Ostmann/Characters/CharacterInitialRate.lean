import OAI.NumberTheory.Ostmann.Characters.CharacterWordAmplitudeLower
import OAI.NumberTheory.Ostmann.Characters.CharacterRepeatRate
import OAI.NumberTheory.Ostmann.Construction.FixedBinEndpointRate

namespace OAI

/-! # The constructed character priors give a uniform initial amplitude -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

/-- The exponent depends on the endpoint and word rates, but not on the
number of selected nonword cells. That number only changes the threshold. -/
theorem eventual_character_initial_rate (k nc : ℕ)
    (a b z Cmass Ctotal Aend Bword B_D c s γ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 ≤ z)
    (hCmass : 0 ≤ Cmass) (hCtotal : 0 ≤ Ctotal) (hc : 1 ≤ c)
    (hs : 0 < s) (hγ : 0 < γ) (hbudget : 4 * nc * Cmass ≤ z)
    (hgap : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B_D) (ψ : 𝓢(ℝ, ℂ)) :
    ∀ᶠ m : ℕ in atTop, ∀ (r : Fin k → ℕ) (f : ℕ)
      (cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
      (L logX τ : ℝ), 0 < L → (m : ℝ) ≤ z * L → z * L ≤ 2 * m →
      ∀ (P B T₀ : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ) (R : Fin nc → Finset ℕ),
      Q 0 = T₀ → (∀ i : Fin m, Q i.succ = B) →
      (∀ i, Q i ⊆ P) → (∀ i, R i ⊆ P) →
      a * L ≤ ∑ p ∈ B, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
      (∀ i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R i, (p : ℝ)⁻¹) →
      (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
      ∀ (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ),
      (∀ i p, p ∈ R (cell i) → cellLo i ≤ p ∧ p ≤ cellHi i) →
      ∀ (T : Fin k → ℝ) (anchor : Fin k → Bool → ℝ)
        (bin : Fin (⌊4 * τ⌋₊ + 1)),
      let Δ := (B_D + 20 * Real.log z) * m
      let C := (Fintype.card (CharacterRole k) : ℝ) * c
      (∀ v, Real.exp (characterLogCenter bin.val T anchor
        (characterFillerTarget logX Δ bin.val T anchor) (true, some v) - c) ≤
          ∏ i, cellLo ⟨v, i⟩) →
      (∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤ Real.exp (characterLogCenter bin.val T anchor
        (characterFillerTarget logX Δ bin.val T anchor) (true, some v) + c)) →
      (∀ y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P,
        productPrior (fun i => primeSubsetPrior P
          (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
        (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
        (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).2.1 i : ℝ)) ≤ 4 * τ) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ≠ 1) →
      ∀ (t : ∀ p : ℕ, ZMod p) (E : Finset ℤ) (ρ H : ℝ),
      Real.sqrt (Real.exp logX) * Real.exp (-Aend * m) ≤ E.card →
      Real.exp (-Bword * m) ≤ ρ →
      (∀ x, 0 ≤ (ψ x).re) → (∀ x, (ψ x).im = 0) → 0 ≤ H →
      (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp logX)).re) →
      (∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
        (fun _ p => χ p ((x : ZMod p) - t p))
        (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) →
      (∀ x ∈ E, ∀ i, γ ≤
        ‖∑ p : P, (primeSubsetPrior P (R i) p : ℂ) * χ p ((x : ZMod p) - t p)‖) →
      ∀ N : ℕ, (∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) →
      (∀ p ∈ P, H * Real.exp (Δ + C) < p) → H * Real.exp (Δ + C) ≤ N →
      Real.exp (-(Aend + 2 * Bword + 2) * m) ≤
        ‖wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
          (fun i => primeSubsetPrior P (R i)) χ t ψ (Real.exp logX) N
          (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖ := by
  let B₀ := Aend + 2 * Bword + 1
  let C := (Fintype.card (CharacterRole k) : ℝ) * c
  filter_upwards [eventual_character_repeat_rate nc a b z Cmass Ctotal B₀ B_D C
      ha hb hz hCmass hCtotal hbudget hgap ψ,
    eventual_fixed_bin_endpoint_rate nc s γ Aend Bword hs hγ,
    eventually_ge_atTop (1 : ℕ)] with m hrepeat hend hm
  intro r f cell L logX τ hL hmL hLm P B T₀ hP Q R hzero hsucc hQP hRP hB hT hR hPmass
    cellLo cellHi hcell T anchor bin Δ C' hlo hhi hbin χ hχ t E ρ H hE hρ hψ hreal hH
    hsE hword hmean N hsupp hsmall hN
  have hQpos (i : Fin (m + 1)) : 0 < ∑ p ∈ Q i, (p : ℝ)⁻¹ := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hzero]
      exact hb.trans_le hT
    · rw [hsucc]
      exact (mul_pos ha hL).trans_le hB
  have hRpos (i : Fin nc) : 0 < ∑ p ∈ R i, (p : ℝ)⁻¹ :=
    (Real.exp_pos _).trans_le (hR i)
  have hraw := character_word_amplitude_lower k m nc r f cell P hP Q R hQP hRP
    (fun i => (hQpos i).ne') (fun i => (hRpos i).ne') cellLo cellHi hcell logX Δ τ c hc
    T anchor bin hlo hhi hbin χ hχ t E ψ s ρ γ H hψ hreal
    ((Real.exp_pos _).le.trans hρ) hγ.le hH hsE hword hmean N hsupp hsmall hN
  have hroot : 0 < Real.sqrt (Real.exp logX) := Real.sqrt_pos.mpr (Real.exp_pos _)
  have hmain := hend ((E.card : ℝ) / Real.sqrt (Real.exp logX)) ρ
    ((le_div_iff₀ hroot).mpr (by simpa only [mul_comm] using hE)) hρ
  have herr := hrepeat L (Cmass * L) hL hmL hLm P B T₀ Q R hzero hsucc hB hT
    (by simpa only [neg_mul] using hR) le_rfl hPmass
  have hraw' : (E.card : ℝ) / Real.sqrt (Real.exp logX) *
      (s * ρ ^ 2 * γ ^ (2 * nc)) - wordRepeatFactor P Q R ψ (Δ - C') ≤
      ‖wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
        (fun i => primeSubsetPrior P (R i)) χ t ψ (Real.exp logX) N
        (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖ := by
    convert hraw using 1
    dsimp only [wordRepeatFactor]
    field_simp
    ring
  have he : B₀ + 1 = Aend + 2 * Bword + 2 := by dsimp [B₀]; ring
  simpa only [he] using initial_amplitude_uniform_lower _ _ _ B₀ m hm hmain herr hraw'

end Ostmann

end OAI
