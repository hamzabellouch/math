import OAI.Geometry.NodalSets.Elliptic.ReciprocalFrequencyBound
import OAI.Geometry.NodalSets.Elliptic.RoundDenominatorDerivatives

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

theorem round_denominator_finite_bound {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (u : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u → ∀ (n : ℕ), 0 < n →
      ∀ (x : Yau.Jets.Coord), x ∈ Q → ∀ (H : ℝ), 0 < H →
      (∀ i, i ≤ r+1 → ‖iteratedFDeriv ℝ i u x‖ ≤ A*(n:ℝ)^(i+3)*H) →
      ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i (roundCorrectionDenominator u n) x‖ ≤
        C*(n:ℝ)^(i+8)*H^2 := by
  have hb (i : Fin (r+1)) := round_denominator_derivative_bound hQ i.val hA
  choose c hc hbound using hb
  let C : ℝ := 1+∑ i, c i
  have hc0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ ↦ (hc i).le)
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro u hu n hn x hx H hH hub i hi
  have hb := hbound ⟨i,by omega⟩ u hu n hn x hx H hH (fun j hj ↦ hub j (by omega))
  have hsum := Finset.single_le_sum (fun j _ ↦ (hc j).le)
    (Finset.mem_univ (⟨i,by omega⟩ : Fin (r+1)))
  have hci : c ⟨i,by omega⟩ ≤ C := by dsimp [C]; linarith
  exact hb.trans (by gcongr)

theorem round_reciprocal_derivative_bound {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (u : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u → ∀ (n : ℕ), 0 < n →
      ∀ (x : Yau.Jets.Coord), x ∈ Q → ∀ (H : ℝ), 0 < H →
      (∀ i, i ≤ r+1 → ‖iteratedFDeriv ℝ i u x‖ ≤ A*(n:ℝ)^(i+3)*H) →
      ((n:ℝ)^65)⁻¹*H ≤ sourceFirstJetSize u n x →
      ‖iteratedFDeriv ℝ r (fun y ↦ (roundCorrectionDenominator u n y)⁻¹) x‖ ≤
        C*(n:ℝ)^(137*r+128)*(H^2)⁻¹ := by
  obtain ⟨B,hB,hden⟩ := round_denominator_finite_bound hQ r hA
  obtain ⟨C,hC,hrec⟩ := reciprocal_frequency_bound (E := Yau.Jets.Coord) r hB
  refine ⟨C,hC,?_⟩
  intro u hu n hn x hx H hH hub hjet
  exact hrec _ (roundCorrectionDenominator_smooth u hu n) x n H
    (by exact_mod_cast hn) hH (roundCorrectionDenominator_lower u hn x hH hjet)
    (fun i _ hi ↦ hden u hu n hn x hx H hH hub i hi)

theorem round_reciprocal_finite_bound {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (u : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u → ∀ (n : ℕ), 0 < n →
      ∀ (x : Yau.Jets.Coord), x ∈ Q → ∀ (H : ℝ), 0 < H →
      (∀ i, i ≤ r+1 → ‖iteratedFDeriv ℝ i u x‖ ≤ A*(n:ℝ)^(i+3)*H) →
      ((n:ℝ)^65)⁻¹*H ≤ sourceFirstJetSize u n x →
      ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i (fun y ↦ (roundCorrectionDenominator u n y)⁻¹) x‖ ≤
        C*(n:ℝ)^(137*i+128)*(H^2)⁻¹ := by
  have hb (i : Fin (r+1)) := round_reciprocal_derivative_bound hQ i.val hA
  choose c hc hbound using hb
  let C : ℝ := 1+∑ i, c i
  have hc0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ ↦ (hc i).le)
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro u hu n hn x hx H hH hub hjet i hi
  have hb := hbound ⟨i,by omega⟩ u hu n hn x hx H hH
    (fun j hj ↦ hub j (by omega)) hjet
  have hsum := Finset.single_le_sum (fun j _ ↦ (hc j).le)
    (Finset.mem_univ (⟨i,by omega⟩ : Fin (r+1)))
  have hci : c ⟨i,by omega⟩ ≤ C := by dsimp [C]; linarith
  exact hb.trans (by gcongr)

end
end Yau.Target

end OAI
