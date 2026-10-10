import OAI.NumberTheory.DukePrimeDegree.Entropy.RefinedReturnEntropy
import Mathlib.Dynamics.Ergodic.Conservative

namespace OAI

/-! # The actual measurable first-return partition

The positive return levels cover almost every point of the section. The
exceptional nonreturning set is included with the complement of the section
in the zero label, so the resulting partition is defined everywhere.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical
namespace DukePrimeDegree

lemma exists_firstReturnLevel_of_return {Y : Type*} (T : Y → Y) (S : Set Y)
    {x : Y} (hx : x ∈ S) (hr : ∃ m : ℕ, 0 < m ∧ T^[m] x ∈ S) :
    ∃ n, x ∈ firstReturnLevel T S n := by
  let m := Nat.find hr
  have hm : 0 < m ∧ T^[m] x ∈ S := Nat.find_spec hr
  refine ⟨m-1,hx,?_,?_⟩
  · simpa only [Nat.sub_add_cancel (show 1 ≤ m by omega)] using hm.2
  · intro j hj hjm hret
    have hlt : j < Nat.find hr := by change j < m; omega
    exact Nat.find_min hr hlt ⟨hj,hret⟩

theorem ae_section_mem_firstReturnLevel
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {S : Set Y} (hS : MeasurableSet S) :
    ∀ᵐ x ∂μ, x ∈ S → ∃ n, x ∈ firstReturnLevel T S n := by
  filter_upwards [hT.conservative.ae_mem_imp_frequently_image_mem hS.nullMeasurableSet]
    with x hx hxs
  apply exists_firstReturnLevel_of_return T S hxs
  obtain ⟨m,hm,hret⟩ := (frequently_atTop.mp (hx hxs)) 1
  exact ⟨m,by omega,hret⟩

def firstReturnPartitionAtom {Y : Type*} (T : Y → Y) (S : Set Y) : ℕ → Set Y
  | 0 => (⋃ n : ℕ, firstReturnLevel T S n)ᶜ
  | n+1 => firstReturnLevel T S n

lemma firstReturnPartition_covers {Y : Type*} (T : Y → Y) (S : Set Y) (x : Y) :
    ∃ n, x ∈ firstReturnPartitionAtom T S n := by
  classical
  by_cases h : ∃ n, x ∈ firstReturnLevel T S n
  · obtain ⟨n,hn⟩ := h
    exact ⟨n+1,hn⟩
  · exact ⟨0,by simpa only [firstReturnPartitionAtom,mem_compl_iff,mem_iUnion,not_exists] using h⟩

def firstReturnPartitionCode {Y : Type*} (T : Y → Y) (S : Set Y) (x : Y) : ℕ :=
  Nat.find (firstReturnPartition_covers T S x)

lemma firstReturnPartitionCode_mem {Y : Type*} (T : Y → Y) (S : Set Y) (x : Y) :
    x ∈ firstReturnPartitionAtom T S (firstReturnPartitionCode T S x) :=
  Nat.find_spec (firstReturnPartition_covers T S x)

lemma firstReturnPartitionAtom_unique {Y : Type*} (T : Y → Y) (S : Set Y)
    {n m : ℕ} {x : Y} (hn : x ∈ firstReturnPartitionAtom T S n)
    (hm : x ∈ firstReturnPartitionAtom T S m) : n=m := by
  cases n with
  | zero =>
      cases m with
      | zero => rfl
      | succ m => exact (hn (mem_iUnion.mpr ⟨m,hm⟩)).elim
  | succ n =>
      cases m with
      | zero => exact (hm (mem_iUnion.mpr ⟨n,hn⟩)).elim
      | succ m => exact congrArg Nat.succ (firstReturnLevel_unique T S hn hm)

lemma firstReturnPartitionCode_eq_iff {Y : Type*} (T : Y → Y) (S : Set Y)
    (x : Y) (n : ℕ) :
    firstReturnPartitionCode T S x=n ↔ x ∈ firstReturnPartitionAtom T S n := by
  constructor
  · intro h
    simpa only [h] using firstReturnPartitionCode_mem T S x
  · exact firstReturnPartitionAtom_unique T S (firstReturnPartitionCode_mem T S x)

lemma measurable_firstReturnPartitionCode
    {Y : Type*} [MeasurableSpace Y] {T : Y → Y} (hT : Measurable T)
    {S : Set Y} (hS : MeasurableSet S) : Measurable (firstReturnPartitionCode T S) := by
  apply measurable_find (firstReturnPartition_covers T S)
  intro n
  cases n with
  | zero => exact (MeasurableSet.iUnion (fun n => measurableSet_firstReturnLevel hT hS n)).compl
  | succ n => exact measurableSet_firstReturnLevel hT hS n

/-- Passing from section membership to the first-return code does not
change equality of future itineraries (EL, paragraph 7.49). -/
lemma firstReturnPartitionCode_eq_of_future_section
    {Y : Type*} (T : Y → Y) (S : Set Y) (x y : Y)
    (hxy : ∀ k : ℕ, T^[k] x ∈ S ↔ T^[k] y ∈ S) :
    firstReturnPartitionCode T S x=firstReturnPartitionCode T S y := by
  have hlevel (n : ℕ) : x ∈ firstReturnLevel T S n ↔ y ∈ firstReturnLevel T S n := by
    constructor
    · rintro ⟨hx,hret,havoid⟩
      refine ⟨(hxy 0).mp hx,(hxy (n+1)).mp hret,?_⟩
      intro j hj hjn hy
      exact havoid j hj hjn ((hxy j).mpr hy)
    · rintro ⟨hy,hret,havoid⟩
      refine ⟨(hxy 0).mpr hy,(hxy (n+1)).mpr hret,?_⟩
      intro j hj hjn hx
      exact havoid j hj hjn ((hxy j).mp hx)
  have hmem : y ∈ firstReturnPartitionAtom T S (firstReturnPartitionCode T S x) := by
    have hx := firstReturnPartitionCode_mem T S x
    cases hc : firstReturnPartitionCode T S x with
    | zero =>
        rw [hc] at hx
        change y ∉ ⋃ n : ℕ, firstReturnLevel T S n
        intro hy
        obtain ⟨n,hn⟩ := mem_iUnion.mp hy
        exact hx (mem_iUnion.mpr ⟨n,(hlevel n).mpr hn⟩)
    | succ n =>
        rw [hc] at hx
        exact (hlevel n).mp hx
  exact (firstReturnPartitionCode_eq_iff T S y _).mpr hmem |>.symm

lemma firstReturnPartitionCode_future_eq_of_future_section
    {Y : Type*} (T : Y → Y) (S : Set Y) (x y : Y)
    (hxy : ∀ k : ℕ, T^[k] x ∈ S ↔ T^[k] y ∈ S) :
    ∀ k : ℕ, firstReturnPartitionCode T S (T^[k] x)=
      firstReturnPartitionCode T S (T^[k] y) := by
  intro k
  apply firstReturnPartitionCode_eq_of_future_section
  intro j
  simpa only [←Function.iterate_add_apply] using hxy (j+k)

/-- The everywhere-defined return code has finite Shannon entropy. -/
theorem firstReturnPartitionCode_information_summable
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S) :
    Summable (fun n => Real.negMulLog (μ.real {x | firstReturnPartitionCode T S x=n})) := by
  have hs := firstReturnPartition_information_summable μ hT hE hS
  have he (n : ℕ) : {x | firstReturnPartitionCode T S x=n+1}=firstReturnLevel T S n := by
    ext x
    exact firstReturnPartitionCode_eq_iff T S x (n+1)
  apply (summable_nat_add_iff 1).mp
  simpa only [he] using hs

end DukePrimeDegree

end

end OAI
