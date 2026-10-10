import OAI.NumberTheory.TwoPoint.Bounds.MixedDifference

namespace OAI

/-! Exact singleton centering on selected coordinates of the complete residue sample. -/

namespace TwoPointCorrelations

open Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

noncomputable def selectedMixedDifference (S : Finset ι) (a : ι → A)
    (F : (ι → A) → ℝ) (x : ι → A) : ℝ :=
  mixedDifference (fun i : S => a i)
    (fun z : S → A => F (joinCoordinates S z (fun i : {i // i ∉ S} => x i)))
    (fun i : S => x i)

omit [Fintype ι] [Fintype A] [DecidableEq A] in
lemma selectedMixedDifference_join (S : Finset ι) (a : ι → A) (F : (ι → A) → ℝ)
    (x : S → A) (y : {i // i ∉ S} → A) :
    selectedMixedDifference S a F (joinCoordinates S x y) =
      mixedDifference (fun i : S => a i) (fun z => F (joinCoordinates S z y)) x := by
  simp only [selectedMixedDifference, joinCoordinates_mem, joinCoordinates_notMem]

omit [Fintype ι] [Fintype A] [DecidableEq A] in
lemma selectedMixedDifference_bound (S : Finset ι) (a : ι → A) (F : (ι → A) → ℝ)
    (hF : ∀ x, |F x| ≤ 1) (x : ι → A) :
    |selectedMixedDifference S a F x| ≤ 2 ^ S.card := by
  simpa only [selectedMixedDifference, Fintype.card_coe] using
    abs_mixedDifference_le (fun i : S => a i)
      (fun z : S → A => F (joinCoordinates S z (fun i : {i // i ∉ S} => x i)))
      (fun z => hF _) (fun i : S => x i)

namespace FiniteLaw

/-- The unselected coordinates remain part of the original sample, and
are simply held fixed while applying the exact centering identity. -/
theorem exact_selected_centering (μ : ι → FiniteLaw A) (S : Finset ι)
    (a : ι → A) (F : (ι → A) → ℝ) :
    (independent μ).average (fun x =>
      (∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x) =
      (∏ i ∈ S, (μ i).weight (a i)) *
        (independent μ).average (selectedMixedDifference S a F) := by
  rw [independent_average_split μ S]
  have hinner (y : {i // i ∉ S} → A) :
      (independent (fun i : S => μ i)).average (fun x : S → A =>
        (∏ i ∈ S, ((if joinCoordinates S x y i = a i then (1 : ℝ) else 0) -
          (μ i).weight (a i))) * F (joinCoordinates S x y)) =
      (∏ i ∈ S, (μ i).weight (a i)) *
        (independent (fun i : S => μ i)).average
          (mixedDifference (fun i : S => a i) (fun x => F (joinCoordinates S x y))) := by
    have hh := exact_mixed_centering (fun i : S => μ i) (fun i : S => a i)
      (fun x => F (joinCoordinates S x y))
    have hp (x : S → A) :
        (∏ i ∈ S, ((if joinCoordinates S x y i = a i then (1 : ℝ) else 0) -
          (μ i).weight (a i))) =
        ∏ i : S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i)) := by
      rw [← prod_coe_sort S]
      simp only [joinCoordinates_mem]
    simp_rw [hp]
    rw [← prod_coe_sort S]
    exact hh
  simp_rw [hinner]
  rw [average_const_mul, independent_average_split μ S (selectedMixedDifference S a F)]
  simp only [selectedMixedDifference_join]

/-- Nonsingletons with at least one lit occurrence are forced once. The
singleton coordinates are then centered on the same sample. -/
theorem exact_selected_designation (μ : ι → FiniteLaw A) (S T : Finset ι)
    (hST : Disjoint S T) (a b : ι → A) (F : (ι → A) → ℝ) :
    (independent μ).average (fun x =>
      (∏ i ∈ T, if x i = b i then (1 : ℝ) else 0) *
      ((∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x)) =
      (∏ i ∈ T, (μ i).weight (b i)) * (∏ i ∈ S, (μ i).weight (a i)) *
        (independent μ).average
          (selectedMixedDifference S a (fun x => F (forceCoordinates T b x))) := by
  rw [independent_forcing μ T b]
  have hp (x : ι → A) :
      (∏ i ∈ S, ((if forceCoordinates T b x i = a i then (1 : ℝ) else 0) -
        (μ i).weight (a i))) =
      ∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i)) := by
    apply prod_congr rfl
    intro i hi
    have hiT : i ∉ T := fun hiT => (disjoint_left.mp hST hi hiT)
    simp only [forceCoordinates_apply, hiT, ite_false]
  simp_rw [hp]
  rw [exact_selected_centering μ S a]
  ring

/-- The absolute value is taken only after singleton integration, retaining
the full cancellation caused by the mixed difference. -/
theorem selected_designation_bound (μ : ι → FiniteLaw A) (S T : Finset ι)
    (hST : Disjoint S T) (a b : ι → A) (F : (ι → A) → ℝ) :
    |(independent μ).average (fun x =>
      (∏ i ∈ T, if x i = b i then (1 : ℝ) else 0) *
      ((∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x))| ≤
      (∏ i ∈ T, (μ i).weight (b i)) * (∏ i ∈ S, (μ i).weight (a i)) *
        (independent μ).average (fun x =>
          |selectedMixedDifference S a (fun x => F (forceCoordinates T b x)) x|) := by
  rw [exact_selected_designation μ S T hST a b F, abs_mul,
    abs_of_nonneg (mul_nonneg (prod_nonneg (fun i _ => (μ i).nonneg _))
      (prod_nonneg (fun i _ => (μ i).nonneg _)))]
  exact mul_le_mul_of_nonneg_left (abs_average_le _ _)
    (mul_nonneg (prod_nonneg (fun i _ => (μ i).nonneg _))
      (prod_nonneg (fun i _ => (μ i).nonneg _)))

end FiniteLaw

end TwoPointCorrelations

end OAI
