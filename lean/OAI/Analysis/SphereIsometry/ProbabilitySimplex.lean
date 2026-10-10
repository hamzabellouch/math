import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Finite probability simplices

The coordinates are nonnegative real numbers with sum one. The positive-coordinate
selection lemma is the boundary-compatible labelling rule used in Sperner's argument.
-/

open scoped BigOperators

namespace Tingley

def probabilitySimplexSet (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

theorem convex_probabilitySimplexSet (ι : Type*) [Fintype ι] :
    Convex ℝ (probabilitySimplexSet ι) := by
  intro left hleft right hright first second hfirst hsecond hsum
  refine ⟨fun index => add_nonneg (mul_nonneg hfirst (hleft.1 index))
    (mul_nonneg hsecond (hright.1 index)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hleft.2, hright.2, mul_one, hsum]

theorem single_mem_probabilitySimplexSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (index : ι) : Pi.single index 1 ∈ probabilitySimplexSet ι :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ => le_rfl⟩, by simp⟩

theorem mem_Icc_of_mem_probabilitySimplexSet {ι : Type*} [Fintype ι]
    {weights : ι → ℝ} (hweights : weights ∈ probabilitySimplexSet ι) (index : ι) :
    weights index ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hweights.1 index, hweights.2 ▸
    Finset.single_le_sum (fun other _ => hweights.1 other) (Finset.mem_univ index)⟩

abbrev ProbabilitySimplex (ι : Type*) [Fintype ι] := ↥(probabilitySimplexSet ι)

instance probabilitySimplex_compactSpace (ι : Type*) [Fintype ι] :
    CompactSpace (ProbabilitySimplex ι) := by
  apply isCompact_iff_compactSpace.mp
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (0 : ι → ℝ) 1))
  · change IsClosed ({weights : ι → ℝ | ∀ index, 0 ≤ weights index} ∩
      {weights | ∑ index, weights index = 1})
    apply IsClosed.inter
    · rw [Set.ofPred_forall]
      exact isClosed_iInter fun index =>
        isClosed_le continuous_const (continuous_apply index)
    · exact isClosed_eq (by fun_prop) continuous_const
  · intro weights hweights
    exact ⟨fun index => (mem_Icc_of_mem_probabilitySimplexSet hweights index).1,
      fun index => (mem_Icc_of_mem_probabilitySimplexSet hweights index).2⟩

namespace ProbabilitySimplex

variable {ι : Type*} [Fintype ι]

theorem coordinate_nonneg (a : ProbabilitySimplex ι) (i : ι) : 0 ≤ a.val i :=
  a.property.1 i

theorem sum_coordinates (a : ProbabilitySimplex ι) : ∑ i, a.val i = 1 :=
  a.property.2

noncomputable def pointMass (i : ι) : ProbabilitySimplex ι := by
  classical
  exact ⟨Pi.single i 1, single_mem_probabilitySimplexSet i⟩

instance [Nonempty ι] : Nonempty (ProbabilitySimplex ι) :=
  ⟨pointMass (Classical.choice ‹Nonempty ι›)⟩

theorem exists_positive_coordinate (a : ProbabilitySimplex ι) :
    ∃ i, 0 < a.val i := by
  classical
  by_contra h
  have hz : a.val = 0 := by
    funext i
    exact le_antisymm (le_of_not_gt (fun hi => h ⟨i, hi⟩)) (a.coordinate_nonneg i)
  have hs := a.sum_coordinates
  simp [hz] at hs

theorem eq_of_coordinate_le (a b : ProbabilitySimplex ι)
    (hab : ∀ i, a.val i ≤ b.val i) : a = b := by
  classical
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ b.val i - a.val i :=
    fun i _ => sub_nonneg.mpr (hab i)
  have hsum : ∑ i, (b.val i - a.val i) = 0 := by
    rw [Finset.sum_sub_distrib, b.sum_coordinates, a.sum_coordinates, sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  apply Subtype.ext
  funext i
  exact (sub_eq_zero.mp (hz i (Finset.mem_univ i))).symm

end ProbabilitySimplex

theorem exists_positive_dominating_coordinate {ι : Type*} [Fintype ι]
    (a b : ProbabilitySimplex ι) :
    ∃ i, 0 < a.val i ∧ b.val i ≤ a.val i := by
  classical
  by_contra h
  have hstrict : ∀ i, 0 < a.val i → a.val i < b.val i := by
    intro i hi
    exact lt_of_not_ge (fun hle => h ⟨i, hi, hle⟩)
  have hweak : ∀ i, a.val i ≤ b.val i := by
    intro i
    by_cases hi : 0 < a.val i
    · exact (hstrict i hi).le
    · have hz : a.val i = 0 :=
        le_antisymm (le_of_not_gt hi) (a.coordinate_nonneg i)
      rw [hz]
      exact b.coordinate_nonneg i
  obtain ⟨i, hi⟩ := a.exists_positive_coordinate
  have hsum : (∑ j, a.val j) < ∑ j, b.val j :=
    Finset.sum_lt_sum (fun j _ => hweak j) ⟨i, Finset.mem_univ i, hstrict i hi⟩
  rw [a.sum_coordinates, b.sum_coordinates] at hsum
  exact (lt_irrefl (1 : ℝ)) hsum

end Tingley

end OAI
