import OAI.NumberTheory.Ostmann.Supply.FiniteParseval

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

def largeSpectrum (S : Finset (ZMod p)) : Finset (ZMod p) :=
  Finset.univ.filter (fun v => 1 < ‖additiveTransform S v‖)

@[simp] theorem mem_largeSpectrum (S : Finset (ZMod p)) (v : ZMod p) :
    v ∈ largeSpectrum S ↔ 1 < ‖additiveTransform S v‖ := by
  simp [largeSpectrum]

@[simp] theorem zero_not_mem_largeSpectrum (S : Finset (ZMod p)) :
    0 ∉ largeSpectrum S := by simp [additiveTransform_zero]

@[simp] theorem neg_mem_largeSpectrum (S : Finset (ZMod p)) (v : ZMod p) :
    -v ∈ largeSpectrum S ↔ v ∈ largeSpectrum S := by
  simp [additiveTransform_neg]

theorem sum_norm_additiveTransform (S : Finset (ZMod p)) :
    ∑ v, ‖additiveTransform S v‖ = gamma S * p := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  exact (div_mul_cancel₀ _ hp).symm

theorem largeSpectrum_card_le (S : Finset (ZMod p)) :
    ((largeSpectrum S).card : ℝ) ≤ gamma S * p := by
  rw [← sum_norm_additiveTransform]
  calc
    ((largeSpectrum S).card : ℝ) = ∑ v ∈ largeSpectrum S, (1 : ℝ) := by simp
    _ ≤ ∑ v ∈ largeSpectrum S, ‖additiveTransform S v‖ :=
      Finset.sum_le_sum fun v hv => (mem_largeSpectrum S v |>.mp hv).le
    _ ≤ ∑ v, ‖additiveTransform S v‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => norm_nonneg _)

theorem largeSpectrum_energy_le_complement (S : Finset (ZMod p)) :
    ∑ v ∈ (largeSpectrum S)ᶜ, ‖additiveTransform S v‖^2 ≤ gamma S * p := by
  rw [← sum_norm_additiveTransform]
  calc
    (∑ v ∈ (largeSpectrum S)ᶜ, ‖additiveTransform S v‖^2) ≤
        ∑ v ∈ (largeSpectrum S)ᶜ, ‖additiveTransform S v‖ := by
      apply Finset.sum_le_sum
      intro v hv
      have hh : ‖additiveTransform S v‖ ≤ 1 := by
        simpa only [Finset.mem_compl, mem_largeSpectrum, not_lt] using hv
      nlinarith [norm_nonneg (additiveTransform S v)]
    _ ≤ ∑ v, ‖additiveTransform S v‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => norm_nonneg _)

theorem largeSpectrum_energy_ge (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1) :
    (1 - gamma S) * p ≤ ∑ v ∈ largeSpectrum S, ‖additiveTransform S v‖^2 := by
  have hsplit := Finset.sum_add_sum_compl (largeSpectrum S)
    (fun v => ‖additiveTransform S v‖^2)
  rw [additiveTransform_parseval S hpos hlt] at hsplit
  have hrem := largeSpectrum_energy_le_complement S
  nlinarith

theorem sparse_transform_concentration (S : Finset (ZMod p))
    (hpos : 0 < density S) (hlt : density S < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hg : gamma S ≤ ε^2) :
    ((largeSpectrum S).card : ℝ) ≤ ε * p ∧
      (1 - ε^2) * p ≤ ∑ v ∈ largeSpectrum S, ‖additiveTransform S v‖^2 := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  constructor
  · calc
      _ ≤ gamma S * p := largeSpectrum_card_le S
      _ ≤ ε^2 * p := mul_le_mul_of_nonneg_right hg hp
      _ ≤ ε * p := mul_le_mul_of_nonneg_right (by nlinarith) hp
  · calc
      _ ≤ (1-gamma S)*p := mul_le_mul_of_nonneg_right (by linarith) hp
      _ ≤ _ := largeSpectrum_energy_ge S hpos hlt

end Ostmann.Supply

end

end OAI
