import Mathlib.Order.Preorder.Finite
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Basic.ENNReal.BigOperators

namespace OAI

/-! A finite laminar Carleson family packs on the union of every selected
subfamily. Repeated occurrences are allowed; maximal geometric sets are
counted only once. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LipschitzHilbert

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

theorem finite_laminar_carleson_packing (Q : ι → Set X) (mu : Measure X)
    (hQ : ∀ i, MeasurableSet (Q i))
    (hlam : ∀ i j, Q i⊆Q j ∨ Q j⊆Q i ∨ Disjoint (Q i) (Q j))
    (a : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (hcar : ∀ j, (∑ i, if Q i⊆Q j then a i else 0)≤C*mu (Q j))
    (I : Finset ι) :
    (∑ i∈I, a i)≤C*mu (⋃ i∈I, Q i) := by
  classical
  let F : Finset (Set X) := I.image Q
  let R := F.filter (fun A => Maximal (fun B => B∈F) A)
  have hcover (i : ι) (hi : i∈I) : ∃ A∈R, Q i⊆A := by
    obtain ⟨A,hiA,hmax⟩ := F.exists_le_maximal (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    exact ⟨A,Finset.mem_filter.mpr ⟨hmax.1,hmax⟩,hiA⟩
  have hrepr {A : Set X} (hA : A∈R) : ∃ i∈I, Q i=A :=
    Finset.mem_image.mp (Finset.mem_filter.mp hA).1
  have hdisj : (↑R : Set (Set X)).PairwiseDisjoint id := by
    intro A hA B hB hne
    obtain ⟨i,hi,rfl⟩ := hrepr hA
    obtain ⟨j,hj,rfl⟩ := hrepr hB
    rcases hlam i j with hij | hji | hd
    · have he : Q i=Q j := subset_antisymm hij ((Finset.mem_filter.mp hA).2.2
        (Finset.mem_filter.mp hB).1 hij)
      exact (hne he).elim
    · have he : Q i=Q j := subset_antisymm ((Finset.mem_filter.mp hB).2.2
        (Finset.mem_filter.mp hA).1 hji) hji
      exact (hne he).elim
    · exact hd
  have hmeas (A : Set X) (hA : A∈R) : MeasurableSet A := by
    obtain ⟨i,_,rfl⟩ := hrepr hA
    exact hQ i
  have hunion : (⋃ A∈R, A)=(⋃ i∈I, Q i) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨A,hA,hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨i,hi,rfl⟩ := hrepr hA
      exact mem_iUnion₂.mpr ⟨i,hi,hx⟩
    · intro x hx
      obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨A,hA,hisub⟩ := hcover i hi
      exact mem_iUnion₂.mpr ⟨A,hA,hisub hx⟩
  calc
    _ ≤ ∑ i∈I, ∑ A∈R, if Q i⊆A then a i else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨A,hA,hisub⟩ := hcover i hi
      calc
        a i = if Q i⊆A then a i else 0 := (ite_eq_left hisub).symm
        _ ≤ _ := Finset.single_le_sum (a:=A) (f:=fun B : Set X => if Q i⊆B then a i else 0) (fun _ _ => zero_le) hA
    _ = ∑ A∈R, ∑ i∈I, if Q i⊆A then a i else 0 := Finset.sum_comm
    _ ≤ ∑ A∈R, ∑ i, if Q i⊆A then a i else 0 := by
      apply Finset.sum_le_sum
      intro A _
      exact Finset.sum_le_univ_sum_of_nonneg (fun _ => zero_le)
    _ ≤ ∑ A∈R, C*mu A := by
      apply Finset.sum_le_sum
      intro A hA
      obtain ⟨i,_,rfl⟩ := hrepr hA
      exact hcar i
    _ = C*mu (⋃ i∈I, Q i) := by
      have hm : mu (⋃ A∈R, A)=∑ A∈R, mu A := by
        simpa only [id_eq] using (measure_biUnion_finset (μ:=mu) hdisj hmeas)
      rw [←Finset.mul_sum,←hm,hunion]

end LipschitzHilbert

end

end OAI
