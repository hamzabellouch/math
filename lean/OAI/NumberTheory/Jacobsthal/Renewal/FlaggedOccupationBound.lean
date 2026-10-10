import OAI.NumberTheory.Jacobsthal.Paths.FlaggedSourceStart

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FlaggedOccupationBound

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag

variable {α : Type*} [MeasurableSpace α]

noncomputable def selected (f : α → ℝ≥0∞) : FlagState α → ℝ≥0∞ :=
  failed.indicator (fun z => f z.1)

theorem selected_measurable {f : α → ℝ≥0∞} (hf : Measurable f) : Measurable (selected f) :=
  (hf.comp measurable_fst).indicator failed_measurable

omit [MeasurableSpace α] in
@[simp] theorem selected_false (f : α → ℝ≥0∞) (x : α) : selected f (x,false) = 0 := by
  simp [selected,failed]

omit [MeasurableSpace α] in
@[simp] theorem selected_true (f : α → ℝ≥0∞) (x : α) : selected f (x,true) = f x := by
  simp [selected,failed]

theorem selected_integral_le {f : α → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hf : ∀ x,f x ≤ C) (μ : Measure (FlagState α)) :
    (∫⁻ z,selected f z ∂μ) ≤ C*μ failed := by
  calc
    _ ≤ ∫⁻ z,C*failed.indicator (fun _ => (1:ℝ≥0∞)) z ∂μ := by
      apply lintegral_mono
      rintro ⟨x,b⟩
      cases b <;> simp [selected,failed,hf x]
    _ = _ := by
      rw [lintegral_const_mul' _ _ hC,lintegral_indicator failed_measurable,setLIntegral_const,one_mul]

theorem selected_true_integral (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {f : α → ℝ≥0∞} (hf : Measurable f) (x : α) :
    (∫⁻ z,selected f z ∂marked K hBad (x,true)) = ∫⁻ y,f y ∂K x := by
  rw [marked_eq_map K hBad (x,true),lintegral_map (selected_measurable hf)
    (row_update_measurable hBad true)]
  simp only [Bool.true_or,selected_true]

theorem selected_row (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {q V : α → ℝ≥0∞} (hV : Measurable V)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : ∀ x,V x ≤ C)
    (hdrift : ∀ x,q x+(∫⁻ y,V y ∂K x) ≤ V x) (z : FlagState α) :
    selected q z+(∫⁻ y,selected V y ∂marked K hBad z)+
      C*failed.indicator (fun _ => (1:ℝ≥0∞)) z ≤
        selected V z+C*marked K hBad z failed := by
  rcases z with ⟨x,b⟩
  cases b with
  | false =>
    simpa [selected,failed] using selected_integral_le hC hbound (marked K hBad (x,false))
  | true =>
    rw [selected_true,selected_true,selected_true_integral K hBad hV,marked_failed_true]
    simpa [failed] using add_le_add_left (hdrift x) C

theorem law_selected_step (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {q V : α → ℝ≥0∞} (hq : Measurable q) (hV : Measurable V)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : ∀ x,V x ≤ C)
    (hdrift : ∀ x,q x+(∫⁻ y,V y ∂K x) ≤ V x) (x : α) (n : ℕ) :
    (∫⁻ z,selected q z ∂law K hBad x n)+
      (∫⁻ z,selected V z ∂law K hBad x (n+1))+C*law K hBad x n failed ≤
        (∫⁻ z,selected V z ∂law K hBad x n)+C*law K hBad x (n+1) failed := by
  have hp : (marked K hBad)^(n+1) = marked K hBad ∘ₖ ((marked K hBad)^n) := pow_succ' _ _
  have hnext : (∫⁻ z,selected V z ∂law K hBad x (n+1)) =
      ∫⁻ z,∫⁻ y,selected V y ∂marked K hBad z ∂law K hBad x n := by
    unfold law
    rw [hp,Kernel.lintegral_comp _ _ _ (selected_measurable hV)]
  have hfail : law K hBad x (n+1) failed = ∫⁻ z,marked K hBad z failed ∂law K hBad x n := by
    unfold law
    rw [hp,Kernel.comp_apply' _ _ _ failed_measurable]
  have hi := lintegral_mono (μ := law K hBad x n) (selected_row K hBad hV hC hbound hdrift)
  have hinner : Measurable (fun z => ∫⁻ y,selected V y ∂marked K hBad z) := (selected_measurable hV).lintegral_kernel
  rw [lintegral_add_left (f := fun z => selected q z+(∫⁻ y,selected V y ∂marked K hBad z))
      ((selected_measurable hq).add hinner),
    lintegral_add_left (selected_measurable hq),
    lintegral_add_left (selected_measurable hV),
    lintegral_const_mul' _ _ hC,lintegral_const_mul' _ _ hC,
    lintegral_indicator failed_measurable,setLIntegral_const,one_mul] at hi
  rw [← hnext,← hfail] at hi
  exact hi

theorem finite_selected_occupation (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {q V : α → ℝ≥0∞} (hq : Measurable q) (hV : Measurable V)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : ∀ x,V x ≤ C)
    (hdrift : ∀ x,q x+(∫⁻ y,V y ∂K x) ≤ V x) (x : α) (N : ℕ) :
    (∑ n ∈ range N, ∫⁻ z,selected q z ∂law K hBad x n) ≤ C*law K hBad x N failed := by
  have hstrong : ∀ N : ℕ,
      (∑ n ∈ range N, ∫⁻ z,selected q z ∂law K hBad x n)+
        (∫⁻ z,selected V z ∂law K hBad x N) ≤ C*law K hBad x N failed := by
    intro N
    induction N with
    | zero =>
      simp only [sum_range_zero,zero_add,law,pow_zero]
      change (∫⁻ z,selected V z ∂Measure.dirac (x,false)) ≤ C*Measure.dirac (x,false) failed
      rw [lintegral_dirac' _ (selected_measurable hV),selected_false]
      exact zero_le
    | succ N ih =>
      rw [sum_range_succ,add_assoc]
      have hd : C*law K hBad x N failed ≠ ∞ := ENNReal.mul_ne_top hC (measure_ne_top _ _)
      apply (ENNReal.add_le_add_iff_right hd).mp
      calc
        _ = (∑ n ∈ range N, ∫⁻ z,selected q z ∂law K hBad x n)+
            ((∫⁻ z,selected q z ∂law K hBad x N)+
             (∫⁻ z,selected V z ∂law K hBad x (N+1))+C*law K hBad x N failed) := by ac_rfl
        _ ≤ (∑ n ∈ range N, ∫⁻ z,selected q z ∂law K hBad x n)+
            ((∫⁻ z,selected V z ∂law K hBad x N)+C*law K hBad x (N+1) failed) :=
          add_le_add_right (law_selected_step K hBad hq hV hC hbound hdrift x N) _
        _ ≤ C*law K hBad x N failed+C*law K hBad x (N+1) failed := by
          rw [← add_assoc]
          exact add_le_add_left ih _
        _ = _ := add_comm _ _
  exact (le_add_right le_rfl).trans (hstrong N)

end NumberTheoryLean.FlaggedOccupationBound

end

end Erdos970

end OAI
