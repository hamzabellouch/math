import OAI.NumberTheory.Ostmann.Construction.InitialGapRate

namespace OAI

/-! # Repeated-prime loss for the actual top-first character word -/
namespace Ostmann
open Filter
open scoped Classical BigOperators FourierTransform SchwartzMap

/-- The character word puts the top prime first. Its normalizer is the same
as the bulk-first ordering used in the elementary repeat estimate. -/
theorem character_wordRepeatFactor_eq {m c : ℕ} (P B T : Finset ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (R : Fin c → Finset ℕ)
    (hzero : Q 0 = T) (hsucc : ∀ i : Fin m, Q i.succ = B)
    (ψ : 𝓢(ℝ, ℂ)) (D : ℝ) :
    wordRepeatFactor P Q R ψ D =
      wordRepeatFactor P (Fin.append (fun _ : Fin m => B) (fun _ : Fin 1 => T)) R ψ D := by
  have hprod : (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) =
      (∑ p ∈ T, (p : ℝ)⁻¹)⁻¹ * (∑ p ∈ B, (p : ℝ)⁻¹)⁻¹ ^ m := by
    rw [Fin.prod_univ_succ, hzero]
    simp only [hsucc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold wordRepeatFactor
  rw [doubledRole_normalizers, doubledRole_normalizers, hprod]
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_one]
  ring

theorem eventual_character_repeat_rate (c : ℕ) (a b z A C B₀ B_D E : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 ≤ z) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hc : 4 * c * A ≤ z)
    (hgap : 2 * ((2 * Real.log (3 / a) + 3 + 2 * C) + B₀ + 2) ≤ B_D)
    (ψ : 𝓢(ℝ, ℂ)) :
    ∀ᶠ m : ℕ in atTop, ∀ L J : ℝ, 0 < L →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m →
      ∀ (P B T : Finset ℕ) (Q : Fin (m + 1) → Finset ℕ) (R : Fin c → Finset ℕ),
      Q 0 = T → (∀ i : Fin m, Q i.succ = B) →
      a * L ≤ ∑ p ∈ B, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T, (p : ℝ)⁻¹ →
      (∀ i, Real.exp (-J) ≤ ∑ p ∈ R i, (p : ℝ)⁻¹) → J ≤ A * L →
      (∑ p : P, (p : ℝ)⁻¹) ≤ C * L →
      wordRepeatFactor P Q R ψ ((B_D + 20 * Real.log z) * m - E) ≤
        Real.exp (-(B₀ + 1) * m) := by
  have hz0 : 0 < z := by linarith
  filter_upwards [eventual_wordRepeatFactor_bound c a b z A C ha hb hz0 hA hC ψ,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (E / 2)] with m hm hE
  intro L J hL hmL hLm P B T Q R hzero hsucc hB hT hR hJ hP
  rw [character_wordRepeatFactor_eq P B T Q R hzero hsucc]
  apply (hm L J _ hL hmL hLm P B T R hB hT hR hJ hP).trans
  exact initial_gap_rate _ _ B₀ B_D z E m hz
    (initial_repeat_coefficient a z A C c ha hz hC hc) hE hgap

end Ostmann

end OAI
