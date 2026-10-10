import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroPartialSums
import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedFiniteLogDerivative

namespace OAI

/-! # Reindexing finite disk divisor sums by the faithful zero copies -/

namespace Ostmann

open Filter
open scoped Topology BigOperators Classical

noncomputable def ComplexZeroEnumeration.diskIndices {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (R : ℝ) : Finset ℕ :=
  (Z.heightIndices (2 * R)).filter (fun i => ‖Z.zeros i‖ ≤ 2 * R)

@[simp] theorem ComplexZeroEnumeration.mem_diskIndices {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (R : ℝ) (i : ℕ) :
    i ∈ Z.diskIndices R ↔ ‖Z.zeros i‖ ≤ 2 * R := by
  simp only [ComplexZeroEnumeration.diskIndices, Finset.mem_filter, Z.mem_heightIndices]
  exact and_iff_right_of_imp (fun h => (Complex.abs_im_le_norm _).trans h)

theorem ComplexZeroEnumeration.tendsto_diskIndices {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) : Tendsto Z.diskIndices atTop atTop := by
  apply tendsto_atTop.2
  intro S
  have hh : ∀ᶠ R : ℝ in atTop, ∀ i ∈ S, ‖Z.zeros i‖ ≤ R :=
    (Filter.eventually_all_finset S).mpr (fun i _ => eventually_ge_atTop _)
  filter_upwards [hh, eventually_ge_atTop 0] with R hR hR0
  intro i hi
  exact (Z.mem_diskIndices R i).mpr (by linarith [hR i hi])

theorem characterZeroEnumeration_disk_sum (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) (R : ℝ) (W : ℂ → ℂ) :
    (∑ z ∈ completedDiskZeros χ R, (analyticOrderNatAt χ.completed z : ℂ) * W z) =
      ∑ i ∈ (characterZeroEnumeration χ e).diskIndices R,
        W ((characterZeroEnumeration χ e).zeros i) := by
  let Z := characterZeroEnumeration χ e
  have ho (z : ℂ) (hz : z ∈ criticalZerosUpTo χ (2 * R)) :
      analyticOrderNatAt χ.completed z = analyticOrderNatAt χ.L z :=
    (congrArg ENat.toNat (χ.L_order_eq_completed z (mem_criticalZerosUpTo.mp hz).1.1)).symm
  unfold completedDiskZeros ComplexZeroEnumeration.diskIndices
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    _ = ∑ z ∈ criticalZerosUpTo χ (2 * R),
        (analyticOrderNatAt χ.L z : ℂ) * (if ‖z‖ ≤ 2 * R then W z else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [ho z hz]
      split_ifs <;> simp
    _ = _ := characterZeroEnumeration_height_sum χ e (2 * R) _

theorem completedZeroPartialFraction_index_sum (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) (R : ℝ) (s : ℂ) :
    completedZeroPartialFraction χ R s =
      ∑ i ∈ (characterZeroEnumeration χ e).diskIndices R,
        (s - (characterZeroEnumeration χ e).zeros i)⁻¹ := by
  simpa only [completedZeroPartialFraction, div_eq_mul_inv] using
    characterZeroEnumeration_disk_sum χ e R (fun z => (s - z)⁻¹)

end Ostmann

end OAI
