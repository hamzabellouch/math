import Mathlib

namespace OAI

noncomputable section

namespace Problem310.Aux
open Set MeasureTheory

/-- Integer-periodization of a subset of the line. -/
def integerPeriodize (U : Set ℝ) : Set ℝ :=
  ⋃ k : ℤ, (fun x : ℝ => x + (k : ℝ)) ⁻¹' U

theorem isOpen_integerPeriodize (U : Set ℝ) (hU : IsOpen U) :
    IsOpen (integerPeriodize U) := by
  exact isOpen_iUnion fun k => hU.preimage (continuous_id.add continuous_const)

theorem integerPeriodize_onePeriodic (U : Set ℝ) :
    ∀ x : ℝ, x + 1 ∈ integerPeriodize U ↔ x ∈ integerPeriodize U := by
  intro x
  simp only [integerPeriodize, mem_iUnion, mem_preimage]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    convert hk using 1
    push_cast
    ring
  · rintro ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    convert hk using 1
    push_cast
    ring

/-- Periodization cannot increase the measure within a fundamental interval
beyond the measure of the original subset. -/
theorem volume_integerPeriodize_le (U : Set ℝ) (hU : MeasurableSet U) :
    volume (integerPeriodize U ∩ Icc (0 : ℝ) 1) ≤ volume U := by
  have hae : (integerPeriodize U ∩ Icc (0 : ℝ) 1 : Set ℝ) =ᵐ[volume]
      (integerPeriodize U ∩ Ico (0 : ℝ) 1 : Set ℝ) :=
    Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl Ico_ae_eq_Icc.symm
  rw [measure_congr hae]
  have hpiece (k : ℤ) :
      volume (((fun x : ℝ => x + (k : ℝ)) ⁻¹' U) ∩ Ico (0 : ℝ) 1) =
        volume (U ∩ Ico (k : ℝ) ((k : ℝ) + 1)) := by
    have hI : (fun x : ℝ => x + (k : ℝ)) ⁻¹' Ico (k : ℝ) ((k : ℝ) + 1) =
        Ico (0 : ℝ) 1 := by
      ext x
      simp only [mem_preimage, mem_Ico]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [← hI, ← preimage_inter]
    exact measure_preimage_add_right volume (k : ℝ) _
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun k : ℤ => U ∩ Ico (k : ℝ) ((k : ℝ) + 1))) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro x hx hy
    rcases lt_or_gt_of_ne hij with h | h
    · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
        exact_mod_cast (show i + 1 ≤ j by omega)
      linarith [hx.2.2, hy.2.1]
    · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by
        exact_mod_cast (show j + 1 ≤ i by omega)
      linarith [hy.2.2, hx.2.1]
  have hunion : (⋃ k : ℤ, U ∩ Ico (k : ℝ) ((k : ℝ) + 1)) = U := by
    rw [← inter_iUnion, iUnion_Ico_intCast, inter_univ]
  calc
    volume (integerPeriodize U ∩ Ico (0 : ℝ) 1)
        = volume (⋃ k : ℤ, ((fun x : ℝ => x + (k : ℝ)) ⁻¹' U) ∩ Ico (0 : ℝ) 1) := by
          rw [integerPeriodize, iUnion_inter]
    _ ≤ ∑' k : ℤ, volume (((fun x : ℝ => x + (k : ℝ)) ⁻¹' U) ∩ Ico (0 : ℝ) 1) :=
      measure_iUnion_le _
    _ = ∑' k : ℤ, volume (U ∩ Ico (k : ℝ) ((k : ℝ) + 1)) := tsum_congr hpiece
    _ = volume (⋃ k : ℤ, U ∩ Ico (k : ℝ) ((k : ℝ) + 1)) :=
      (measure_iUnion hdisj (fun k => hU.inter measurableSet_Ico)).symm
    _ = volume U := congrArg volume hunion

/-- An arbitrarily small open periodic enlargement of a periodic set. -/
theorem exists_open_periodic_envelope (R : Set ℝ)
    (hR : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ENNReal) (hε : ε ≠ 0) :
    ∃ V : Set ℝ, R ⊆ V ∧ IsOpen V ∧
      (∀ x : ℝ, x + 1 ∈ V ↔ x ∈ V) ∧
      volume (V ∩ Icc (0 : ℝ) 1) ≤ volume (R ∩ Icc (0 : ℝ) 1) + ε := by
  obtain ⟨U, hRU, hU, hμU⟩ :=
    (R ∩ Icc (0 : ℝ) 1).exists_isOpen_le_add volume hε
  refine ⟨integerPeriodize U, ?_, isOpen_integerPeriodize U hU,
    integerPeriodize_onePeriodic U, (volume_integerPeriodize_le U hU.measurableSet).trans hμU⟩
  intro x hx
  have hper : Function.Periodic (fun y : ℝ => y ∈ R) 1 := fun y => propext (hR y)
  have hmem : x - (⌊x⌋ : ℝ) ∈ R := by
    have heq := hper.sub_int_mul_eq (x := x) ⌊x⌋
    simpa using heq.mpr hx
  have hfrac : x - (⌊x⌋ : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Int.floor_le x)
    · have h := Int.lt_floor_add_one x
      linarith
  apply mem_iUnion.2
  refine ⟨-⌊x⌋, ?_⟩
  simpa only [mem_preimage, Int.cast_neg, ← sub_eq_add_neg] using hRU ⟨hmem, hfrac⟩

end Problem310.Aux

end

end OAI
