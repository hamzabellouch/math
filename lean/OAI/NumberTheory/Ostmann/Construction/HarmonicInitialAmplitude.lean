import OAI.NumberTheory.Ostmann.Construction.WordGraphAmplitude
import OAI.NumberTheory.Ostmann.Construction.HarmonicInitialStatistic

namespace OAI

/-! # Positive endpoints give an actual finite initial graph amplitude -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

noncomputable def wordRepeatFactor {k m : ℕ} (P : Finset ℕ)
    (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ) (ψ : 𝓢(ℝ, ℂ)) (D : ℝ) : ℝ :=
  ‖𝓕 ψ 0‖ * (∏ i, (∑ p ∈ Fin.append (Fin.append Q R) (Fin.append Q R) i, (p : ℝ)⁻¹)⁻¹) *
    (((k + m) + (k + m) : ℕ) : ℝ) ^ ((k + m) + (k + m)) *
    Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2)

theorem harmonic_initial_amplitude {B : Type*} [Fintype B] [Nonempty B] {k m : ℕ}
    [Nonempty (Fin ((k + m) + (k + m)))]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ i, R i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ p ∈ Q i, (p : ℝ)⁻¹)
    (hRmass : ∀ i, 0 < ∑ p ∈ R i, (p : ℝ)⁻¹)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (t : ∀ p : ℕ, ZMod p) (E : Finset ℕ) (ψ : 𝓢(ℝ, ℂ))
    (X H U D : ℝ) (hX : 0 < X) (hH : 0 ≤ H) (hU : 0 < U)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hψreal : ∀ x, (ψ x).im = 0)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ p ∈ P, H * U < p) (N : ℕ) (hN : H * U ≤ N)
    (bin : (Fin k → P) → B) (c δ γ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hword : ∀ a ∈ E, ∀ i, δ * (∑ p ∈ Q i, (p : ℝ)⁻¹) ≤
      ∑ p ∈ Q i, (p : ℝ)⁻¹ * (χ p ((a : ZMod p) - t p)).re)
    (hcell : ∀ a ∈ E, ∀ i, γ * (∑ p ∈ R i, (p : ℝ)⁻¹) ≤
      ∑ p ∈ R i, (p : ℝ)⁻¹ * (χ p ((a : ZMod p) - t p)).re)
    (hupper : ∀ b x, x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b → (∏ i, (x i : ℝ)) ≤ X * U)
    (hlower : ∀ b x, x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b → X * Real.exp D ≤ ∏ i, (x i : ℝ)) :
    ∃ b : B, ((E.card : ℝ) / Fintype.card B *
        (c * (δ ^ k / Fintype.card B) ^ 2 * γ ^ (2 * m))) / Real.sqrt X -
      wordRepeatFactor P Q R ψ D ≤
      ‖wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
        (fun j => primeSubsetPrior P (R j)) χ t ψ X N bin b‖ := by
  let μ := fun i => primeSubsetPrior P (Q i)
  let ν := fun i => primeSubsetPrior P (R i)
  obtain ⟨b, hb⟩ := harmonic_initial_statistic P Q R hQ hR hQmass hRmass
    (fun a p => χ p ((a : ZMod p) - t p)) (fun a p _ => (χ p).norm_le_one _)
    E ψ X hX bin c δ γ hc hδ hγ hψ hcE
    (by simpa only [Int.cast_natCast] using hword)
    (by simpa only [Int.cast_natCast] using hcell)
  have hstat := word_statistic_eq_character_mean Subtype.val μ ν χ t ψ X hX hψreal bin b
  rw [hstat] at hb
  have herr := word_character_repeat_removal P hP Q R χ hχ t ψ X H U D hX hU hsupp
    hsmall bin b (hupper b) (hlower b)
  have hcut (x : Fin ((k + m) + (k + m)) → P) (hx : x ∈ wordCharacterEvent μ ν bin b) :
      H * (∏ i, (x i : ℕ)) ≤ N * X := by
    calc
      H * (∏ i, (x i : ℕ)) = H * ∏ i, (x i : ℝ) := by simp only [Nat.cast_prod]
      _ ≤ H * (X * U) := mul_le_mul_of_nonneg_left (hupper b x hx) hH
      _ = (H * U) * X := by ring
      _ ≤ N * X := mul_le_mul_of_nonneg_right hN hX.le
  have hη := wordGraphAmplitude_eq P hP μ ν χ hχ t ψ X H hX N hsupp bin b hcut
  have hl := initial_amplitude_lower _ _ _ X _ (Real.sqrt X * wordRepeatFactor P Q R ψ D)
    hX hb herr hη
  refine ⟨b, ?_⟩
  convert hl using 1
  field_simp [(Real.sqrt_pos.mpr hX).ne']

end Ostmann

end OAI
