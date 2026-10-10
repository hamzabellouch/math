import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroPartialSums

namespace OAI

/-! # Convergence of the actual contour zero sum -/

namespace Ostmann

open Filter Finset
open scoped Topology BigOperators Classical

theorem smoothZeroTerm_summable_of_multiplicity {Z : ∀ χ, ComplexZeroEnumeration χ}
    (χ : PrimitiveComplexCharacter) (hZ : (Z χ).RespectsMultiplicity)
    (X : ℝ) (hX : 2 ≤ X) : Summable (fun i => ‖smoothZeroTerm Z χ X i‖) := by
  obtain ⟨C, hC, hM⟩ := primeMeanMellin_decay
  let D : ℝ := 32 / Real.log (14 / 13)
  have hD : 0 ≤ D := le_of_lt (div_pos (by norm_num) (Real.log_pos (by norm_num)))
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have hcount (S : Finset ℕ) (T : ℝ) (hT : 0 ≤ T) :
      ((S.filter (fun i => |((Z χ).zeros i).im| ≤ T)).card : ℝ) ≤
        D * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)) := by
    have hsub : (S.filter fun i => |((Z χ).zeros i).im| ≤ T) ⊆ (Z χ).heightIndices T := by
      intro i hi
      exact ((Z χ).mem_heightIndices T i).mpr (mem_filter.mp hi).2
    calc
      _ ≤ ((Z χ).count 0 T : ℝ) := by
        rw [(Z χ).count_zero_eq_card]
        exact_mod_cast card_le_card hsub
      _ ≤ _ := (Z χ).count_bound_of_multiplicity hZ T hT
  apply summable_of_sum_le (fun i => norm_nonneg _)
    (c := (X * C) * (2 * (2 * D * (Real.log χ.modulus + 3)) ^ 2))
  intro S
  have hh := finite_high_zero_tail_bound S (fun i => |((Z χ).zeros i).im|)
    (χ.modulus : ℝ) D 0 hq hD le_rfl (fun _ _ => abs_nonneg _) (hcount S)
  simp only [add_zero, Real.log_one, mul_zero, Real.exp_zero, mul_one] at hh
  calc
    _ ≤ ∑ i ∈ S, (X * C) * Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) :=
      sum_le_sum (fun i _ => smoothZeroTerm_bound_of_mellin C hM χ X (by linarith) i)
    _ = (X * C) * ∑ i ∈ S, Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) :=
      (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

theorem smoothContourWeight_eq_zeroTerm (Z : ∀ χ, ComplexZeroEnumeration χ)
    (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 0 < X) (i : ℕ) :
    smoothContourWeight X ((Z χ).zeros i) = smoothZeroTerm Z χ X i := by
  rw [smoothContourWeight, smoothZeroTerm, Complex.cpow_def_of_ne_zero (by exact_mod_cast hX.ne')]
  rw [← Complex.ofReal_log hX.le]
  congr 2
  ring

theorem smoothActualZeroSum_tendsto (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ)
    (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 2 ≤ X) :
    Tendsto (fun T : ℝ => ∑ z ∈ criticalZerosUpTo χ T,
      (analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z) atTop
      (𝓝 (∑' i, smoothZeroTerm (fun ψ => characterZeroEnumeration ψ (e ψ)) χ X i)) := by
  let Z := fun ψ => characterZeroEnumeration ψ (e ψ)
  have hs := (smoothZeroTerm_summable_of_multiplicity (Z := Z) χ
    (characterZeroEnumeration_respectsMultiplicity χ (e χ)) X hX).of_norm
  have ht := (Z χ).tendsto_height_sum (fun i => smoothZeroTerm Z χ X i) hs
  convert ht using 1
  funext T
  rw [characterZeroEnumeration_height_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact smoothContourWeight_eq_zeroTerm Z χ X (by linarith) i

end Ostmann

end OAI
