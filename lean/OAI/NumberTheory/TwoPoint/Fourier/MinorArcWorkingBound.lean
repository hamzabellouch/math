import OAI.NumberTheory.TwoPoint.Fourier.MinorArcParameterRanges
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcWorkingBand

namespace OAI

/-! The typical minor-arc estimate at the common working length. Both
the fourth-root saving and the prime-square remainder fit one rate. -/
namespace TwoPointCorrelations

open Finset

theorem minor_arc_typical_working_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ {ι : Type*} (I : Finset ι) (P : ι → Finset ℕ),
      (∀ i ∈ I, ∀ p ∈ P i, p.Prime) → Set.PairwiseDisjoint (I:Set ι) P →
      ∀ i ∈ I, ∀ X H : ℕ, 2 ≤ H → H ≤ X →
      1 ≤ Real.log (H:ℝ) → 1 ≤ Real.log (Real.log (H:ℝ)) →
      ∀ W : ℝ, 1 ≤ W → Real.log (H:ℝ) ≤ W^(1/5:ℝ) →
      (∀ p ∈ P i, p ≠ 2 ∧ 2*R₀ ≤ p ∧ 2*W ≤ (p:ℝ) ∧ (p:ℝ) ≤ (H:ℝ)/W) →
      ∀ F : ℕ → ℂ, Multiplicative F → OneBounded F →
      ∀ r : ℤ, ∀ q : ℕ, 2 ≤ q → W ≤ (q:ℝ) → (q:ℝ) ≤ (H:ℝ)/W →
      ∀ α : ℝ, IsCoprime (q:ℤ) r → |α-(r:ℝ)/q| ≤ 1/(q:ℝ)^2 →
      shortExponentialIntegral (mrtTypicalCoefficient I P F) X H α ≤
        C*(X:ℝ)*H*majorArcWorkingError W := by
  obtain ⟨C,hC,R₀,hbound⟩ := minor_arc_typical_parameter_range_saving
  refine ⟨C+12,by positivity,R₀,?_⟩
  intro ι I P hP hdis i hi X H hH hHX hLH hLL W hW hcap hrange F hFm hFb r q hq hWq hqH α hcop happ
  have hW0 : 0 < W := by linarith
  have hR : 0 < ⌈W⌉₊ := Nat.ceil_pos.mpr hW0
  have hpr : ∀ p ∈ P i, ⌈W⌉₊ ≤ p ∧ p ≤ H := by
    intro p hp
    have hr := hrange p hp
    refine ⟨Nat.ceil_le.mpr (by linarith [hr.2.2.1]),?_⟩
    exact_mod_cast hr.2.2.2.trans (div_le_self (Nat.cast_nonneg H) hW)
  have htail : (∑ p ∈ P i, 1/(p:ℝ)^2) ≤ 2/W := by
    apply (minor_arc_square_reciprocal_sum (P i) ⌈W⌉₊ H hR hpr).trans
    exact div_le_div_of_nonneg_left (by norm_num) hW0 (Nat.le_ceil W)
  have hworking := major_arc_minor_working_rate hW hLH hcap
  have hinv : W⁻¹ ≤ majorArcWorkingError W := by
    calc
      _ = W^(-1:ℝ) := (Real.rpow_neg_one W).symm
      _ ≤ W^(-1/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hW (by norm_num)
      _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg hW0.le _)
        (by linarith [Real.log_nonneg hW])
  have hx : (X:ℝ)+(H:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast (show X+H ≤ 2*X by omega)
  have hmain := mul_le_mul_of_nonneg_left hworking (show 0 ≤ C*(X:ℝ)*H by positivity)
  have he : 3*(H:ℝ)*(X+H)*(∑ p ∈ P i, 1/(p:ℝ)^2) ≤
      12*(X:ℝ)*H*majorArcWorkingError W := by
    calc
      _ ≤ 3*(H:ℝ)*(X+H)*(2/W) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ 3*(H:ℝ)*(2*X)*(2/W) := by gcongr
      _ = 12*(X:ℝ)*H*W⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
  apply (hbound I P hP hdis i hi X H hH hHX hLH hLL W hW hrange
    F hFm hFb r q hq hWq hqH α hcop happ).trans
  have hh := add_le_add hmain he
  convert hh using 1 <;> ring

end TwoPointCorrelations

end OAI
