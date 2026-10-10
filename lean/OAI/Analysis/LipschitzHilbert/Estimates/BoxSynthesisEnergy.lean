import OAI.Analysis.LipschitzHilbert.Estimates.EnvelopeSynthesis

namespace OAI

/-! The fixed-box energy step in the reference-line concentration proof.
The assumed coefficient budget is the finite local Carleson sum appearing
in equation (src-10); the synthesis estimate is derived from envelopes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem box_synthesis_energy {σ : Type*} {ι : σ → Type*} [Fintype σ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → ℂ) (f : ∀ j, ι j → SchwartzMap ℝ ℂ)
    (s rho : ∀ j, ι j → ℝ) (len : σ → ℝ) (a r C D T B : ℝ) (q : ℕ)
    (hlen : ∀ j, 0 < len j) (hr : 0 < r) (hlenr : ∀ j, ∀ _ : ι j, len j ≤ r)
    (hrho : ∀ j i, 0 < rho j i) (hrhoT : ∀ j i, rho j i ≤ T)
    (hcenter : ∀ j i, |s j i - a| ≤ r) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hover : ∀ j x, ∑ i, rho j i * lineEnvelope (s j i) (len j) (1 + 2 * q) x ≤ D)
    (henv : ∀ j i x, ‖f j i x‖ ≤ C * (rho j i * lineEnvelope (s j i) (len j) (1 + 2 * q) x))
    (hbudget : ∑ j, len j * ∑ i, ‖c j i‖ ^ 2 ≤ B * r) :
    (∑ j, ∫ x, ‖polynomialLocalization a r q (packetSynthesis (c j) (f j)) x‖ ^ 2) ≤
      D * C ^ 2 * 16 ^ q * Real.pi * T * (B * r) := by
  let A := D * C ^ 2 * 16 ^ q * Real.pi
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmass (j : σ) : ∑ i, ‖c j i‖ ^ 2 * rho j i ≤ T * ∑ i, ‖c j i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrhoT j i) (sq_nonneg ‖c j i‖)
  have hbound (j : σ) :
      (∫ x, ‖polynomialLocalization a r q (packetSynthesis (c j) (f j)) x‖ ^ 2) ≤
        (A * T) * (len j * ∑ i, ‖c j i‖ ^ 2) := by
    classical
    by_cases hnonempty : Nonempty (ι j)
    swap
    · let : IsEmpty (ι j) := ⟨fun i => hnonempty ⟨i⟩⟩
      simp [packetSynthesis, polynomialLocalization_apply]
    have h := polynomial_packetSynthesis_energy (c j) (f j) (s j) (rho j)
      a (len j) r C D q (hlen j) hr (hlenr j (Classical.choice hnonempty))
      (hrho j) (hcenter j) hD (hover j) (henv j)
    calc
      _ ≤ A * len j * ∑ i, ‖c j i‖ ^ 2 * rho j i := by
        convert h using 1
        dsimp [A]
        ring
      _ ≤ A * len j * (T * ∑ i, ‖c j i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hmass j) (mul_nonneg hA (hlen j).le)
      _ = _ := by ring
  calc
    _ ≤ ∑ j, (A * T) * (len j * ∑ i, ‖c j i‖ ^ 2) := Finset.sum_le_sum (fun j _ => hbound j)
    _ = (A * T) * (∑ j, len j * ∑ i, ‖c j i‖ ^ 2) := (Finset.mul_sum _ _ _).symm
    _ ≤ (A * T) * (B * r) := mul_le_mul_of_nonneg_left hbudget (mul_nonneg hA hT)
    _ = _ := by rfl

end LipschitzHilbert

end

end OAI
