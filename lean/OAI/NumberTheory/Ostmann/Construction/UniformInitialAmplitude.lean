import OAI.NumberTheory.Ostmann.Construction.InitialGapRate

namespace OAI

/-! # Uniform lower bound for the actual initial graph amplitude -/

namespace Ostmann

open Filter
open scoped BigOperators FourierTransform SchwartzMap Classical

/-- All hypotheses here concern the selected prime sets, their ordinary
harmonic masses, the tested endpoints and the sampled product window. The
conclusion is the manuscript's level-zero amplitude, with a rate independent
of the gap and of the number of fixed cell roles. -/
theorem uniform_initial_amplitude (r : ℕ) (a b z A C c₀ δ γ Aₑ Bₑ B_D E₀ H : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 ≤ z) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hγ : 0 < γ) (hAₑ : 0 ≤ Aₑ) (hBₑ : 0 ≤ Bₑ)
    (hroles : 4 * r * A ≤ z)
    (hgap : 2 * ((2 * Real.log (3 / a) + 3 + 2 * C) +
      (2 * (Aₑ + 3 * Bₑ) - 2 * Real.log δ + 1) + 2) ≤ B_D)
    (hH : 0 ≤ H) (ψ : 𝓢(ℝ, ℂ))
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hψreal : ∀ x, (ψ x).im = 0)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ∀ᶠ m : ℕ in atTop, ∀ (L X J : ℝ), 0 < L → 0 < X →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m → J ≤ A * L →
      ∀ (P U T : Finset ℕ) (R : Fin r → Finset ℕ) (hP : ∀ p ∈ P, p.Prime),
      U ⊆ P → T ⊆ P → (∀ i, R i ⊆ P) →
      a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T, (p : ℝ)⁻¹ →
      (∀ i, Real.exp (-J) ≤ ∑ p ∈ R i, (p : ℝ)⁻¹) →
      (∑ p : P, (p : ℝ)⁻¹) ≤ C * L →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ≠ 1) →
      ∀ (t : ∀ p : ℕ, ZMod p) (E : Finset ℕ)
        (B : Type) [Fintype B] [Nonempty B] (bin : (Fin (m + 1) → P) → B),
      Real.exp (-Aₑ * L) ≤ (E.card : ℝ) / Real.sqrt X →
      (Fintype.card B : ℝ) ≤ Real.exp (Bₑ * L) →
      (∀ e ∈ E, c₀ ≤ (ψ ((e : ℝ) / X)).re) →
      (∀ e ∈ E, ∀ i, δ * (∑ p ∈ Fin.append (fun _ : Fin m => U) (fun _ : Fin 1 => T) i,
        (p : ℝ)⁻¹) ≤ ∑ p ∈ Fin.append (fun _ : Fin m => U) (fun _ : Fin 1 => T) i,
        (p : ℝ)⁻¹ * (χ p ((e : ZMod p) - t p)).re) →
      (∀ e ∈ E, ∀ i, γ * (∑ p ∈ R i, (p : ℝ)⁻¹) ≤
        ∑ p ∈ R i, (p : ℝ)⁻¹ * (χ p ((e : ZMod p) - t p)).re) →
      (∀ p ∈ P, H * Real.exp ((B_D + 20 * Real.log z) * m + E₀) < p) →
      ∀ N : ℕ, H * Real.exp ((B_D + 20 * Real.log z) * m + E₀) ≤ N →
      (∀ b x, x ∈ wordCharacterEvent
        (fun i => primeSubsetPrior P (Fin.append (fun _ : Fin m => U) (fun _ : Fin 1 => T) i))
        (fun i => primeSubsetPrior P (R i)) bin b →
          X * Real.exp ((B_D + 20 * Real.log z) * m - E₀) ≤ ∏ i, (x i : ℝ)) →
      (∀ b x, x ∈ wordCharacterEvent
        (fun i => primeSubsetPrior P (Fin.append (fun _ : Fin m => U) (fun _ : Fin 1 => T) i))
        (fun i => primeSubsetPrior P (R i)) bin b →
          (∏ i, (x i : ℝ)) ≤ X * Real.exp ((B_D + 20 * Real.log z) * m + E₀)) →
      ∃ b, Real.exp (-(2 * (Aₑ + 3 * Bₑ) - 2 * Real.log δ + 2) * m) ≤
        ‖wordGraphAmplitude P hP
          (fun i => primeSubsetPrior P (Fin.append (fun _ : Fin m => U) (fun _ : Fin 1 => T) i))
          (fun i => primeSubsetPrior P (R i)) χ t ψ X N bin b‖ := by
  have hz0 : 0 < z := by linarith
  have hep := eventual_endpoint_statistic_rate r c₀ δ γ Aₑ Bₑ hc₀ hδ hγ hAₑ hBₑ
  have her := eventual_wordRepeatFactor_bound r a b z A C ha hb hz0 hA hC ψ
  have hEcut : ∀ᶠ m : ℕ in atTop, E₀ / 2 ≤ (m : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (E₀ / 2)
  filter_upwards [hep, her, hEcut, eventually_ge_atTop (1 : ℕ)] with m hep her hEcut hm
    L X J hL hX hmL hLm hJ P U T R hP hUP hTP hRP hU hT hR hmass χ hχ t E B _ _ bin hE hBins hcE hword hcell hsmall N hN hlower hupper
  let Q : Fin (m + 1) → Finset ℕ := Fin.append (fun _ : Fin m => U) (fun _ : Fin 1 => T)
  have hQP : ∀ i, Q i ⊆ P := by
    intro i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i
    · simpa [Q] using hUP
    · simpa [Q] using hTP
  have hQmass : ∀ i, 0 < ∑ p ∈ Q i, (p : ℝ)⁻¹ := by
    intro i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i
    · simpa [Q] using (mul_pos ha hL).trans_le hU
    · simpa [Q] using hb.trans_le hT
  let μ := fun i => primeSubsetPrior P (Q i)
  let ν := fun i => primeSubsetPrior P (R i)
  let d := (B_D + 20 * Real.log z) * m
  let B₀ := 2 * (Aₑ + 3 * Bₑ) - 2 * Real.log δ + 1
  let U₀ := Real.exp (d + E₀)
  obtain ⟨bb, hbb⟩ := harmonic_initial_amplitude P hP Q R hQP hRP hQmass
    (fun i => (Real.exp_pos _).trans_le (hR i)) χ hχ t E ψ X H U₀ (d - E₀)
    hX hH (Real.exp_pos _) hψ hψreal hsupp hsmall N hN bin c₀ δ γ
    hc₀.le hδ.le hγ.le hcE hword hcell hupper hlower
  have hL' : L ≤ 2 * m := by nlinarith
  have hS := hep L ((E.card : ℝ) / Real.sqrt X) (Fintype.card B : ℝ) hL'
    (by exact_mod_cast Fintype.card_pos) hE hBins
  have hS' : Real.exp (-B₀ * m) ≤ ((E.card : ℝ) / Fintype.card B *
      (c₀ * (δ ^ (m + 1) / Fintype.card B) ^ 2 * γ ^ (2 * r))) / Real.sqrt X := by
    convert hS using 1
    ring
  have hR' := her L J (d - E₀) hL hmL hLm P U T R hU hT hR hJ hmass
  have hcoef := initial_repeat_coefficient a z A C r ha hz hC hroles
  have hgap' := initial_gap_rate
    (2 * Real.log (3 * z / a) + 2 + (4 * r * A + 2 * C) / z)
    (2 * Real.log (3 / a) + 3 + 2 * C) B₀ B_D z E₀ m hz hcoef hEcut hgap
  have hout := initial_amplitude_uniform_lower _ _ _ B₀ m hm hS' (hR'.trans hgap') hbb
  refine ⟨bb, ?_⟩
  convert hout using 1
  dsimp [B₀]
  congr 2
  ring

end Ostmann

end OAI
