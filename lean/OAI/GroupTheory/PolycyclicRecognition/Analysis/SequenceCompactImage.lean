import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactImageVolume
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Subexponential volume of compact noncritical parameter images -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory Filter
open scoped Topology

theorem subexponential_compact_image_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (n : ℕ) (f : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (df : ℕ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (R L η : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r) (hL : ∀ r, 1 ≤ L r)
    (hη : ∀ r, 0 < η r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R) (hLupper : HasSubexponentialUpperBoundSeq scale L)
    (hηlower : HasSubexponentialLowerBoundSeq scale η)
    (hf : ∀ r z, ‖z‖ ≤ R r + 2 → HasFDerivAt (f r) (df r z) z)
    (hdf : ∀ r z, ‖z‖ ≤ R r + 2 → ‖df r z‖ ≤ L r)
    (hosc : ∀ r z w, ‖z‖ ≤ R r + 2 → ‖w‖ ≤ R r + 2 →
      ‖df r z - df r w‖ ≤ L r * dist z w)
    (K : ℕ → Set (Fin n → ℝ)) (hK : ∀ r, IsCompact (K r))
    (hgood : ∀ r z, z ∈ K r → ‖z‖ ≤ R r ∧ η r ≤ |(df r z).det|)
    (hKlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal)) :
    (∀ r, IsCompact (f r '' K r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (f r '' K r)).toReal) := by
  obtain ⟨C, hC, hb⟩ := exists_compact_image_volume_bound n
  let D := fun r => 8 * (C * L r ^ (n - 1)) * L r
  let ρ := fun r => min 1 (η r / D r)
  have hL0 : ∀ᶠ r in atTop, 0 ≤ L r := Eventually.of_forall (fun r => le_trans zero_le_one (hL r))
  have hD : ∀ r, 0 < D r := by
    intro r
    have hLp : 0 < L r := lt_of_lt_of_le zero_lt_one (hL r)
    dsimp [D]
    positivity
  have hDupper : HasSubexponentialUpperBoundSeq scale D := by
    have hp := hLupper.pow hscale hL0 (n - 1)
    have hcp := (sequence_subexponential_upper_const hscale C).mul hp (Eventually.of_forall (fun _ => hC.le))
    have h8 := (sequence_subexponential_upper_const hscale 8).mul hcp (Eventually.of_forall (by intro r; norm_num))
    exact h8.mul hLupper (Eventually.of_forall (by
      intro r
      have hLp : 0 ≤ L r := le_trans zero_le_one (hL r)
      positivity))
  have hρlower : HasSubexponentialLowerBoundSeq scale ρ :=
    (sequence_subexponential_lower_const hscale zero_lt_one).min
      (hηlower.div hDupper (Eventually.of_forall hD))
  have hρpos (r : ℕ) : 0 < ρ r := lt_min zero_lt_one (div_pos (hη r) (hD r))
  let B := fun r => (2 * R r / ρ r + 2) ^ n
  have hBupper : HasSubexponentialUpperBoundSeq scale B := by
    have h2R := (sequence_subexponential_upper_const hscale 2).mul hRupper
      (Eventually.of_forall (by intro r; norm_num))
    have hquot := h2R.mul hρlower.inv (Eventually.of_forall (fun r => mul_nonneg (by norm_num) (hR r)))
    have hsum := hquot.add (sequence_subexponential_upper_const hscale 2) hscale
    simpa only [B, div_eq_mul_inv] using hsum.pow hscale (Eventually.of_forall (by
      intro r
      have h := hR r
      have h' := hρpos r
      positivity)) n
  have hBpos (r : ℕ) : 0 < B r := by
    have h := hR r
    have h' := hρpos r
    dsimp [B]
    positivity
  have hresult (r : ℕ) := hb (f r) (df r) (R r) (L r) (η r)
    (hR r) (hL r) (hη r) (hf r) (hdf r) (hosc r) (K r) (hK r) (hgood r)
  refine ⟨fun r => (hresult r).1, ?_⟩
  apply ((hηlower.mul hKlower).div hBupper (Eventually.of_forall hBpos)).mono
  apply Eventually.of_forall
  intro r
  apply (div_le_iff₀ (hBpos r)).mpr
  simpa only [B, ρ, D, mul_comm] using (hresult r).2

end PolycyclicRecognition

end

end OAI
