import OAI.NumberTheory.DukePrimeDegree.Dynamics.BoundedReturnCompactSupport
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Positive sections with unbounded return levels

Small positive holes, pulled back over increasingly long orbit segments,
remove only a prescribed amount of mass but preclude bounded return time.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DukePrimeDegree

theorem exists_unbounded_return_section_of_holes
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Ergodic T μ) (hE : MeasurableEmbedding T)
    {A : Set Y} (hA : MeasurableSet A)
    (E : ℕ → Set Y) (hEm : ∀ n, MeasurableSet (E n)) (hEp : ∀ n, μ (E n) ≠ 0)
    (hcost : (∑' n : ℕ, (n+1:ℝ≥0∞)*μ (E n)) < μ A) :
    ∃ S : Set Y, MeasurableSet S ∧ S ⊆ A ∧ μ S ≠ 0 ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ μ (firstReturnLevel T S n) ≠ 0 := by
  let U := ⋃ n : ℕ, ⋃ j : Fin (n+1), T^[j.val] ⁻¹' E n
  have hU : MeasurableSet U := MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun j => (hEm n).preimage (hT.measurable.iterate j.val)
  have hμU : μ U ≤ ∑' n : ℕ, (n+1:ℝ≥0∞)*μ (E n) := by
    apply (measure_iUnion_le _).trans
    apply ENNReal.tsum_le_tsum
    intro n
    apply (measure_iUnion_le _).trans_eq
    simp only [tsum_fintype,(hT.toMeasurePreserving.iterate _).measure_preimage (hEm n).nullMeasurableSet,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  let S := A \ U
  have hS : MeasurableSet S := hA.diff hU
  have hSpos : μ S ≠ 0 := by
    intro hz
    have hcover : A ⊆ S ∪ U := by
      intro x hx
      by_cases hu : x ∈ U
      · exact Or.inr hu
      · exact Or.inl ⟨hx,hu⟩
    have H : μ A ≤ μ S + μ U := (measure_mono hcover).trans (measure_union_le S U)
    rw [hz,zero_add] at H
    exact (not_le_of_gt (hμU.trans_lt hcost)) H
  refine ⟨S,hS,sdiff_subset,hSpos,?_⟩
  intro N
  by_contra hn
  push Not at hn
  have hfull := ae_mem_bounded_return_translates μ hT hE hS hSpos N hn
  have hav : ∀ x ∈ E N, ∀ j < N, x ∉ T^[j] '' S := by
    rintro x hx j hj ⟨y,hy,rfl⟩
    exact hy.2 (mem_iUnion.mpr ⟨N,mem_iUnion.mpr ⟨⟨j,by omega⟩,hx⟩⟩)
  have hz : μ (E N)=0 := measure_eq_zero_iff_ae_notMem.mpr (by
    filter_upwards [hfull] with x hx hxin
    obtain ⟨j,hj,hmem⟩ := hx
    exact hav x hxin j hj hmem)
  exact hEp N hz

/-- Only arbitrarily small positive measurable sets are needed to create
unbounded return levels inside every positive section. -/
theorem exists_unbounded_return_section
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Ergodic T μ) (hE : MeasurableEmbedding T)
    (hsmall : ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ∞ →
      ∃ E : Set Y, MeasurableSet E ∧ μ E ≠ 0 ∧ μ E ≤ ε)
    {A : Set Y} (hA : MeasurableSet A) (hAp : μ A ≠ 0) :
    ∃ S : Set Y, MeasurableSet S ∧ S ⊆ A ∧ μ S ≠ 0 ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ μ (firstReturnLevel T S n) ≠ 0 := by
  have hApos : 0 < μ A := pos_iff_ne_zero.mpr hAp
  let ε : ℕ → ℝ≥0∞ := fun n => (μ A/2)*(2⁻¹)^(n+1)/(n+1)
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp only [ε]
    apply ENNReal.div_pos
    · exact mul_ne_zero (ne_of_gt (ENNReal.div_pos hAp (by norm_num)))
        (pow_ne_zero _ (by norm_num))
    · finiteness
  have hεfin (n : ℕ) : ε n ≠ ∞ := by
    dsimp only [ε]
    finiteness
  choose E hEm hEp hEb using fun n => hsmall (ε n) (hεpos n) (hεfin n)
  apply exists_unbounded_return_section_of_holes μ hT hE hA E hEm hEp
  have hterm (n : ℕ) : (n+1:ℝ≥0∞)*μ (E n) ≤ (μ A/2)*(2⁻¹)^(n+1) := by
    apply (mul_le_mul_of_nonneg_left (hEb n) (show 0 ≤ (n+1:ℝ≥0∞) from zero_le)).trans_eq
    dsimp only [ε]
    rw [mul_comm,ENNReal.div_mul_cancel]
    · positivity
    · finiteness
  have hsum : (∑' n : ℕ, (n+1:ℝ≥0∞)*μ (E n)) ≤ μ A/2 := by
    apply (ENNReal.tsum_le_tsum hterm).trans_eq
    rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric_add_one]
    norm_num
    rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num),mul_one]
  apply hsum.trans_lt
  apply (ENNReal.toReal_lt_toReal (by finiteness) (measure_ne_top μ A)).mp
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using
    half_lt_self (ENNReal.toReal_pos hAp (measure_ne_top μ A))

end DukePrimeDegree

end

end OAI
