import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # A unit interval contains a quantitatively separated height -/

namespace Ostmann

open Set MeasureTheory
open scoped BigOperators

/-- Avoid a finite set of ordinates while retaining a definite distance.
The proof pays only for the total lengths of the forbidden intervals. -/
theorem exists_height_separated (S : Finset ℝ) (T δ : ℝ) (_hδ : 0 < δ)
    (hsize : 2 * δ * (S.card : ℝ) < 1) :
    ∃ t ∈ Ioo T (T + 1), ∀ r ∈ S, δ ≤ |t - r| := by
  classical
  let U : Set ℝ := ⋃ r ∈ S, Ioo (r - δ) (r + δ)
  have hvol : volume U ≤ ENNReal.ofReal (2 * δ * (S.card : ℝ)) := by
    calc
      _ ≤ ∑ r ∈ S, volume (Ioo (r - δ) (r + δ)) := measure_biUnion_finset_le _ _
      _ = ∑ _r ∈ S, ENNReal.ofReal (2 * δ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Real.volume_Ioo]
        congr 1
        ring
      _ = ENNReal.ofReal (2 * δ * (S.card : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul, mul_comm]
  have hnot : ¬Ioo T (T + 1) ⊆ U := by
    intro h
    have hv := (measure_mono h).trans hvol
    rw [Real.volume_Ioo, add_sub_cancel_left] at hv
    norm_num at hv
    exact (not_lt_of_ge hv) hsize
  obtain ⟨t, ht, htu⟩ := Set.not_subset.mp hnot
  refine ⟨t, ht, ?_⟩
  intro r hr
  by_contra hd
  have hd' := abs_lt.mp (lt_of_not_ge hd)
  apply htu
  exact mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hr, by constructor <;> linarith⟩⟩

end Ostmann

end OAI
