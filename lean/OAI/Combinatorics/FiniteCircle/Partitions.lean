import OAI.Combinatorics.FiniteCircle.Windows

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

noncomputable def expect (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * f ω

noncomputable def event (μ : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then μ.weight ω else 0

theorem event_eq_expect (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P] :
    μ.event P = μ.expect (fun ω => if P ω then 1 else 0) := by
  classical
  unfold event expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω <;> simp [h]

theorem expect_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ μ.expect f := Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω))

theorem expect_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    μ.expect f ≤ μ.expect g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω))

@[simp] theorem expect_const (μ : FiniteLaw Ω) (a : ℝ) : μ.expect (fun _ => a) = a := by
  simp only [expect, ← Finset.sum_mul, μ.total, one_mul]

theorem expect_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω + g ω) = μ.expect f + μ.expect g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω - g ω) = μ.expect f - μ.expect g := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_smul (μ : FiniteLaw Ω) (a : ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => a * f ω) = a * μ.expect f := by
  simp only [expect, mul_left_comm _ a, Finset.mul_sum]

theorem expect_sum {ι : Type*} (μ : FiniteLaw Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, μ.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem event_nonneg (μ : FiniteLaw Ω) (P : Ω → Prop) : 0 ≤ μ.event P := by
  classical
  apply Finset.sum_nonneg
  intro ω _
  split <;> first | exact μ.nonneg ω | exact le_rfl

theorem event_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    μ.event P ≤ μ.event Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]
  · exact (hq (h ω hp)).elim
  · exact μ.nonneg ω

@[simp] theorem event_true (μ : FiniteLaw Ω) : μ.event (fun _ => True) = 1 := by
  simp [event, μ.total]

@[simp] theorem event_false (μ : FiniteLaw Ω) : μ.event (fun _ => False) = 0 := by simp [event]

theorem event_le_one (μ : FiniteLaw Ω) (P : Ω → Prop) : μ.event P ≤ 1 := by
  simpa only [event_true] using μ.event_mono (P := P) (Q := fun _ => True) (fun _ _ => trivial)

theorem event_compl (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.event (fun ω => ¬P ω) = 1 - μ.event P := by
  classical
  rw [← μ.total]
  unfold event
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω <;> simp [h]

theorem event_exists_le_sum {ι : Type*} [Fintype ι] (μ : FiniteLaw Ω) (P : ι → Ω → Prop) :
    μ.event (fun ω => ∃ i, P i ω) ≤ ∑ i, μ.event (P i) := by
  classical
  simp only [event_eq_expect]
  rw [← μ.expect_sum]
  apply μ.expect_mono
  intro ω
  by_cases h : ∃ i, P i ω
  · obtain ⟨i, hi⟩ := h
    rw [ite_eq_left ⟨i, hi⟩]
    exact (by simpa only [ite_eq_left hi] using
      (Finset.single_le_sum (f := fun j : ι => if P j ω then (1 : ℝ) else 0)
        (fun j _ => by split <;> norm_num) (Finset.mem_univ i)))
  · simp [show ∀ i, ¬ P i ω from fun i hi => h ⟨i, hi⟩]
end FiniteLaw

noncomputable def selectionWeight {I : Type*} [Fintype I] (q : I → ℝ) (s : I → Bool) : ℝ :=
  ∏ i, if s i then 1 - q i else q i

def selectionLabel {I X : Type*} (c : I → X → Bool) (s : I → Bool) (x : X) : I → Bool :=
  fun i => s i && c i x

theorem selectionWeight_nonneg {I : Type*} [Fintype I] (q : I → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (s : I → Bool) : 0 ≤ selectionWeight q s := by
  apply Finset.prod_nonneg
  intro i _
  split
  · exact sub_nonneg.mpr (hq i).2
  · exact (hq i).1

theorem selectionWeight_total {I : Type*} [Fintype I] [DecidableEq I] (q : I → ℝ) :
    ∑ s : I → Bool, selectionWeight q s = 1 := by
  unfold selectionWeight
  rw [← Fintype.prod_sum (fun i (b : Bool) => if b then 1 - q i else q i)]
  simp

theorem selection_collision {I X : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (c : I → X → Bool) (x y : X) :
    (∑ s : I → Bool, if selectionLabel c s x = selectionLabel c s y then selectionWeight q s else 0) =
      ∏ i, if c i x = c i y then 1 else q i := by
  classical
  have hterm (s : I → Bool) :
      (if selectionLabel c s x = selectionLabel c s y then selectionWeight q s else 0) =
      ∏ i, if (s i && c i x) = (s i && c i y) then
        (if s i then 1 - q i else q i) else 0 := by
    rw [Fintype.prod_ite_zero]
    simp only [selectionLabel, selectionWeight, funext_iff]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun i (b : Bool) =>
    if (b && c i x) = (b && c i y) then (if b then 1 - q i else q i) else 0)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool]
  cases hcx : c i x <;> cases hcy : c i y <;> simp

abbrev PartitionSpace (X : Type*) := (X → Bool) → Bool

theorem finite_partition {X : Type*} [Fintype X] {ρ : X → X → ℝ}
    (hρ : HasCutRepresentation ρ) (α : ℝ) (hα : 0 ≤ α) : by
  classical
  exact ∃ (μ : FiniteLaw (PartitionSpace X)) (label : PartitionSpace X → X → PartitionSpace X),
      ∀ x y, μ.event (fun ω => label ω x = label ω y) = Real.exp (-α * ρ x y) := by
  classical
  obtain ⟨a, ha, hrep⟩ := hρ
  let q : (X → Bool) → ℝ := fun c => Real.exp (-α * a c)
  have hq (c : X → Bool) : 0 ≤ q c ∧ q c ≤ 1 := by
    constructor
    · exact (Real.exp_pos _).le
    · apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) (ha c)
  let μ : FiniteLaw (PartitionSpace X) :=
    ⟨selectionWeight q, selectionWeight_nonneg q hq, selectionWeight_total q⟩
  refine ⟨μ, selectionLabel (fun c => c), ?_⟩
  intro x y
  dsimp only [FiniteLaw.event, μ]
  trans ∏ c : X → Bool, if c x = c y then (1 : ℝ) else q c
  · convert selection_collision q (fun c : X → Bool => c) x y using 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : selectionLabel (fun c : X → Bool => c) ω x = selectionLabel (fun c => c) ω y <;> simp [h]
  have he (c : X → Bool) : (if c x = c y then (1 : ℝ) else q c) =
      Real.exp (-α * (a c * cutDistance c x y)) := by
    by_cases h : c x = c y <;> simp [h, cutDistance, q]
  simp_rw [he]
  rw [← Real.exp_sum, ← Finset.mul_sum]
  congr 2
  exact (hrep x y).symm

theorem partition_separation_le {X Ω Y : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (label : Ω → X → Y) (ρ : X → X → ℝ) (α : ℝ)
    (he : ∀ x y, μ.event (fun ω => label ω x = label ω y) = Real.exp (-α * ρ x y))
    (x y : X) : μ.event (fun ω => label ω x ≠ label ω y) ≤ α * ρ x y := by
  rw [μ.event_compl, he]
  have h := Real.add_one_le_exp (-α * ρ x y)
  linarith

end FiniteCircle

end OAI
