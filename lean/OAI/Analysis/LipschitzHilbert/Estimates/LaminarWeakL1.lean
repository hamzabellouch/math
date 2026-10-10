import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineNesting
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Data.Finset.Max

namespace OAI

/-! The weak L1 covering estimate for a ranked laminar family. Applied
below only to squares in the product of two fixed dyadic grids. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

variable {ι X : Type*}

theorem ranked_disjoint_cover (Q : ι → Set X) (rank : ι → ℤ)
    (hnest : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    (s : Finset ι) : ∃ t : Finset ι, t ⊆ s ∧ (t : Set ι).PairwiseDisjoint Q ∧
      (⋃ i ∈ s, Q i) = ⋃ i ∈ t, Q i := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : s = ∅
    · subst s
      exact ⟨∅,by simp,by simp,by simp⟩
    obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image s rank (Finset.nonempty_iff_ne_empty.mpr hs)
    let r := s.filter (fun j => j ≠ i ∧ Disjoint (Q i) (Q j))
    have hrs : r ⊆ s := Finset.filter_subset _ _
    have hri : i ∉ r := by
      intro hir
      exact (Finset.mem_filter.mp hir).2.1 rfl
    have hstrict : r ⊂ s := (ssubset_iff_subset_ne).mpr ⟨hrs,fun he => hri (he.symm ▸ hi)⟩
    obtain ⟨t,ht,hdisj,hcover⟩ := ih r hstrict
    refine ⟨insert i t,Finset.insert_subset hi (ht.trans hrs),?_,?_⟩
    · intro a ha b hb hab
      by_cases hai : a = i
      · subst a
        have hbt : b ∈ t := (Finset.mem_insert.mp hb).resolve_left (Ne.symm hab)
        exact (Finset.mem_filter.mp (ht hbt)).2.2
      · have hat : a ∈ t := (Finset.mem_insert.mp ha).resolve_left hai
        by_cases hbi : b = i
        · subst b
          exact ((Finset.mem_filter.mp (ht hat)).2.2).symm
        · exact hdisj hat ((Finset.mem_insert.mp hb).resolve_left hbi) hab
    · apply Subset.antisymm
      · intro x hx
        obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hx
        by_cases hji : j = i
        · subst j
          exact mem_iUnion₂.mpr ⟨i,Finset.mem_insert_self _ _,hxj⟩
        by_cases hd : Disjoint (Q i) (Q j)
        · have hxr : x ∈ ⋃ j ∈ r, Q j := mem_iUnion₂.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hji,hd⟩,hxj⟩
          obtain ⟨k,hk,hxk⟩ := mem_iUnion₂.mp (hcover ▸ hxr)
          exact mem_iUnion₂.mpr ⟨k,Finset.mem_insert_of_mem hk,hxk⟩
        · have hint : (Q i ∩ Q j).Nonempty := not_disjoint_iff_nonempty_inter.mp hd
          exact mem_iUnion₂.mpr ⟨i,Finset.mem_insert_self _ _,hnest i j (hmax j hj) hint hxj⟩
      · intro x hx
        obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨j,(Finset.insert_subset hi (ht.trans hrs)) hj,hxj⟩

variable [MeasurableSpace X]

theorem ranked_finite_weak_bound (μ : Measure X) (Q : ι → Set X) (rank : ι → ℤ)
    (hm : ∀ i, MeasurableSet (Q i))
    (hnest : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    (f : X → ℝ≥0∞) (c : ℝ≥0∞) (s : Finset ι)
    (hgood : ∀ i ∈ s, c * μ (Q i) ≤ ∫⁻ x in Q i, f x ∂μ) :
    c * μ (⋃ i ∈ s, Q i) ≤ ∫⁻ x, f x ∂μ := by
  obtain ⟨t,ht,hd,heq⟩ := ranked_disjoint_cover Q rank hnest s
  rw [heq,measure_biUnion_finset hd (fun i _ => hm i),Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ t, ∫⁻ x in Q i, f x ∂μ := Finset.sum_le_sum (fun i hi => hgood i (ht hi))
    _ = ∫⁻ x in ⋃ i ∈ t, Q i, f x ∂μ :=
      (lintegral_biUnion_finset hd (fun i _ => hm i) f).symm
    _ ≤ ∫⁻ x, f x ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl

theorem ranked_countable_weak_bound [Countable ι] (μ : Measure X) (Q : ι → Set X)
    (rank : ι → ℤ) (hm : ∀ i, MeasurableSet (Q i))
    (hnest : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    (f : X → ℝ≥0∞) (c : ℝ≥0∞)
    (hgood : ∀ i, c * μ (Q i) ≤ ∫⁻ x in Q i, f x ∂μ) :
    c * μ (⋃ i, Q i) ≤ ∫⁻ x, f x ∂μ := by
  classical
  have heq : (⋃ i, Q i) = ⋃ s : Finset ι, ⋃ i ∈ s, Q i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨{i},by simpa using hi⟩
    · intro hx
      obtain ⟨s,hs⟩ := mem_iUnion.mp hx
      obtain ⟨i,_,hi⟩ := mem_iUnion₂.mp hs
      exact mem_iUnion.mpr ⟨i,hi⟩
  have hmono : Monotone (fun s : Finset ι => ⋃ i ∈ s, Q i) := by
    intro s t hst x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i,hst hi,hxi⟩
  rw [heq,hmono.measure_iUnion,ENNReal.mul_iSup]
  exact iSup_le (fun s => ranked_finite_weak_bound μ Q rank hm hnest f c s (fun i _ => hgood i))

end LipschitzHilbert

end

end OAI
