import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroCopies
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothTruncatedContour

namespace OAI

/-! # Identifying the finite contour zero sum with the true zero enumeration -/

namespace Ostmann

open Filter
open scoped Topology BigOperators Classical

theorem characterZeroEnumeration_fiber_card (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) (T : ℝ) (z : ℂ)
    (hz : z ∈ criticalZerosUpTo χ T) :
    (((characterZeroEnumeration χ e).heightIndices T).filter
      (fun i => (characterZeroEnumeration χ e).zeros i = z)).card = analyticOrderNatAt χ.L z := by
  have hz' := mem_criticalZerosUpTo.mp hz
  let Z := characterZeroEnumeration χ e
  calc
    _ = (Finset.range (analyticOrderNatAt χ.L z)).card := by
      apply Finset.card_bij (fun i _ => (e i).val.2)
      · intro i hi
        have hzi : (e i).val.1 = z := (Finset.mem_filter.mp hi).2
        exact Finset.mem_range.mpr (hzi ▸ (e i).property.2)
      · intro i hi j hj he
        apply e.injective
        apply Subtype.ext
        exact Prod.ext ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) he
      · intro k hk
        let c : CharacterZeroCopy χ := ⟨(z, k), hz'.1, Finset.mem_range.mp hk⟩
        refine ⟨e.symm c, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
        · change e.symm c ∈ Z.heightIndices T
          rw [Z.mem_heightIndices]
          change |(e (e.symm c)).val.1.im| ≤ T
          simpa [c] using hz'.2
        · change (e (e.symm c)).val.1 = z
          simp [c]
        · simp [c]
    _ = _ := Finset.card_range _

theorem characterZeroEnumeration_height_sum (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) (T : ℝ) (W : ℂ → ℂ) :
    (∑ z ∈ criticalZerosUpTo χ T, (analyticOrderNatAt χ.L z : ℂ) * W z) =
      ∑ i ∈ (characterZeroEnumeration χ e).heightIndices T,
        W ((characterZeroEnumeration χ e).zeros i) := by
  let Z := characterZeroEnumeration χ e
  have hm : ∀ i ∈ Z.heightIndices T, Z.zeros i ∈ criticalZerosUpTo χ T := by
    intro i hi
    exact mem_criticalZerosUpTo.mpr
      ⟨⟨(Z.in_strip i).1, (Z.in_strip i).2, Z.actual_zero i⟩, (Z.mem_heightIndices T i).mp hi⟩
  rw [← Finset.sum_fiberwise_of_maps_to hm (fun i => W (Z.zeros i))]
  apply Finset.sum_congr rfl
  intro z hz
  calc
    (analyticOrderNatAt χ.L z : ℂ) * W z =
        ∑ i ∈ (Z.heightIndices T).filter (fun i => Z.zeros i = z), W z := by
      simp [Z, characterZeroEnumeration_fiber_card χ e T z hz, nsmul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]

theorem ComplexZeroEnumeration.tendsto_heightIndices {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) : Tendsto Z.heightIndices atTop atTop := by
  apply tendsto_atTop.2
  intro S
  have hh : ∀ᶠ T : ℝ in atTop, ∀ i ∈ S, |(Z.zeros i).im| ≤ T :=
    (Filter.eventually_all_finset S).mpr (fun i _ => eventually_ge_atTop _)
  filter_upwards [hh] with T hT
  intro i hi
  exact (Z.mem_heightIndices T i).mpr (hT i hi)

theorem ComplexZeroEnumeration.tendsto_height_sum {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (f : ℕ → ℂ) (hf : Summable f) :
    Tendsto (fun T : ℝ => ∑ i ∈ Z.heightIndices T, f i) atTop (𝓝 (∑' i, f i)) :=
  hf.hasSum.comp Z.tendsto_heightIndices

end Ostmann

end OAI
