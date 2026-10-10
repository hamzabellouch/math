import OAI.NumberTheory.DukePrimeDegree.Entropy.HeightObservationEntropy

namespace OAI

/-! # Averaging the boundaries of shifted height bins

A natural height crosses exactly one of the `q` shifted bin boundaries
when incremented by one. Integrating this identity controls boundary
frequencies without requiring the height itself to be integrable.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree

lemma sum_shifted_height_boundaries (a q : ℕ) (hq : 0 < q) :
    (∑ r ∈ Finset.range q,
      if (a+r+1)/q ≠ (a+r)/q then (1:ℝ) else 0) = 1 := by
  have he (r : ℕ) :
      (if (a+r+1)/q ≠ (a+r)/q then (1:ℝ) else 0) =
        (((a+r+1)/q : ℕ):ℝ) - (((a+r)/q : ℕ):ℝ) := by
    have hlo : (a+r)/q ≤ (a+r+1)/q :=
      Nat.div_le_div_right (show a+r ≤ a+r+1 by omega)
    have hhi : (a+r+1)/q ≤ (a+r)/q+1 := by
      calc
        _ ≤ (a+r+q)/q := Nat.div_le_div_right (by omega)
        _ = _ := Nat.add_div_right _ hq
    by_cases h : (a+r+1)/q = (a+r)/q
    · simp only [h,ne_eq,not_true_eq_false,ite_false,sub_self]
    · have hh : (a+r+1)/q = (a+r)/q+1 := by omega
      rw [ite_eq_left h,hh,Nat.cast_add,Nat.cast_one]
      ring
  simp_rw [he, Nat.add_assoc]
  rw [Finset.sum_range_sub (fun r => (((a+r)/q:ℕ):ℝ))]
  rw [Nat.add_zero,Nat.add_div_right a hq,Nat.cast_add,Nat.cast_one]
  ring

variable {Y : Type*} [MeasurableSpace Y]

def heightBoundary (H : Y → ℕ) (q r : ℕ) : Set Y :=
  {x | (H x+r+1)/q ≠ (H x+r)/q}

lemma measurableSet_heightBoundary {H : Y → ℕ} (hH : Measurable H) (q r : ℕ) :
    MeasurableSet (heightBoundary H q r) :=
  (measurable_of_countable (fun a : ℕ => decide ((a+r+1)/q ≠ (a+r)/q))).comp hH |>
    fun h => by
      have he : heightBoundary H q r =
          (fun x => decide ((H x+r+1)/q ≠ (H x+r)/q)) ⁻¹' {true} := by
        ext x
        simp [heightBoundary]
      rw [he]
      exact h (measurableSet_singleton true)

theorem sum_heightBoundary_measures
    (μ : Measure Y) [IsProbabilityMeasure μ] (H : Y → ℕ) (hH : Measurable H)
    (q : ℕ) (hq : 0 < q) :
    (∑ r ∈ Finset.range q, μ.real (heightBoundary H q r)) = 1 := by
  have hm r := measurableSet_heightBoundary hH q r
  have hi r : Integrable ((heightBoundary H q r).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const 1).indicator (hm r)
  calc
    _ = ∑ r ∈ Finset.range q, ∫ x, (heightBoundary H q r).indicator (fun _ => (1:ℝ)) x ∂μ := by
      apply Finset.sum_congr rfl
      intro r _
      exact (integral_indicator_one (μ := μ) (hm r)).symm
    _ = ∫ x, ∑ r ∈ Finset.range q, (heightBoundary H q r).indicator (fun _ => (1:ℝ)) x ∂μ :=
      (integral_finsetSum _ (fun r _ => hi r)).symm
    _ = 1 := by
      have he (x : Y) : (∑ r ∈ Finset.range q,
          (heightBoundary H q r).indicator (fun _ => (1:ℝ)) x) = 1 := by
        simpa only [heightBoundary,indicator_apply,mem_ofPred_eq] using
          sum_shifted_height_boundaries (H x) q hq
      simp_rw [he]
      simp

theorem exists_shift_heightBoundary_le
    (μ : Measure Y) [IsProbabilityMeasure μ] (H : Y → ℕ) (hH : Measurable H)
    (q : ℕ) (hq : 0 < q) :
    ∃ r < q, μ.real (heightBoundary H q r) ≤ 1/(q:ℝ) := by
  by_contra h
  have hh : ∀ r ∈ Finset.range q, 1/(q:ℝ) < μ.real (heightBoundary H q r) := by
    intro r hr
    exact lt_of_not_ge (fun he => h ⟨r,Finset.mem_range.mp hr,he⟩)
  have hs := Finset.sum_lt_sum (fun r hr => (hh r hr).le)
    ⟨0,Finset.mem_range.mpr hq,hh 0 (Finset.mem_range.mpr hq)⟩
  rw [sum_heightBoundary_measures μ H hH q hq] at hs
  have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,one_div,
    mul_inv_cancel₀ hqr] at hs
  exact (lt_irrefl 1 hs)

omit [MeasurableSpace Y] in
lemma height_bin_change_subset (H : Y → ℕ) (T : Y → Y)
    (hstep : ∀ x, H (T x) ≤ H x+1 ∧ H x ≤ H (T x)+1) (q r : ℕ) :
    {x | (H (T x)+r)/q ≠ (H x+r)/q} ⊆
      heightBoundary H q r ∪ T ⁻¹' heightBoundary H q r := by
  intro x hx
  have hs := hstep x
  change (H (T x)+r)/q ≠ (H x+r)/q at hx
  by_cases he : H (T x)=H x
  · exact (hx (congrArg (fun a => (a+r)/q) he)).elim
  by_cases hlt : H (T x) < H x
  · right
    have hh : H x=H (T x)+1 := by omega
    change (H (T x)+r+1)/q ≠ (H (T x)+r)/q
    have ha : H x+r=H (T x)+r+1 := by omega
    rw [ha] at hx
    exact hx.symm
  · left
    have hh : H (T x)=H x+1 := by omega
    change (H x+r+1)/q ≠ (H x+r)/q
    have ha : H (T x)+r=H x+r+1 := by omega
    rwa [ha] at hx

/-- Coarse height bins can be shifted so their one-step changes have
arbitrarily small probability, even when the height has infinite mean. -/
theorem exists_shift_rare_height_changes
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (H : Y → ℕ) (hH : Measurable H)
    (hstep : ∀ x, H (T x) ≤ H x+1 ∧ H x ≤ H (T x)+1)
    (q : ℕ) (hq : 0 < q) :
    ∃ r < q, μ.real {x | (H (T x)+r)/q ≠ (H x+r)/q} ≤ 2/(q:ℝ) := by
  obtain ⟨r,hr,hb⟩ := exists_shift_heightBoundary_le μ H hH q hq
  refine ⟨r,hr,?_⟩
  have hm := measurableSet_heightBoundary hH q r
  have he : μ.real (T ⁻¹' heightBoundary H q r) = μ.real (heightBoundary H q r) :=
    congrArg ENNReal.toReal (hT.measure_preimage hm.nullMeasurableSet)
  calc
    _ ≤ μ.real (heightBoundary H q r ∪ T ⁻¹' heightBoundary H q r) :=
      measureReal_mono (height_bin_change_subset H T hstep q r) (measure_ne_top _ _)
    _ ≤ μ.real (heightBoundary H q r) + μ.real (T ⁻¹' heightBoundary H q r) :=
      measureReal_union_le _ _
    _ = 2*μ.real (heightBoundary H q r) := by rw [he]; ring
    _ ≤ 2/(q:ℝ) := by
      calc
        _ ≤ 2*(1/(q:ℝ)) := mul_le_mul_of_nonneg_left hb (by norm_num)
        _ = _ := by ring

end DukePrimeDegree

end

end OAI
