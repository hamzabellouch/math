import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseMap
import OAI.Combinatorics.KMedian.Sparse.SparseCardinalRounding
import OAI.Combinatorics.KMedian.Sparse.SparseSupport
import OAI.Combinatorics.KMedian.Sparse.SparseWeightedRounding

namespace OAI

section
section
namespace MetricKMedian.SparseTargetSubset
open Finset RationalWeightedStep
variable {n : ℕ}

def initial (D : Finset (Fin n)) (q : ℚ) : Vector ℚ n :=
  Vector.ofFn (fun i => if i∈D then q else 0)

@[simp] theorem point_initial (D : Finset (Fin n)) (q : ℚ) (i : Fin n) :
    point (initial D q) i=(if i∈D then q else 0) := by
  simp only [initial,point,Vector.getElem_ofFn,Fin.eta]

theorem initial_unit (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1) :
    ∀ i, 0 ≤ point (initial D q) i ∧ point (initial D q) i ≤ 1 := by
  intro i
  rw [point_initial]
  split_ifs
  · exact hq
  · exact ⟨le_rfl,zero_le_one⟩

def vectors (D : Finset (Fin n)) (q : ℚ) : SparseIntegerLaw (Vector ℚ n) :=
  SparseWeightedRounding.round (fun _ => 1) (fun _ => by norm_num) (initial D q)

def law (D : Finset (Fin n)) (q : ℚ) : SparseIntegerLaw (Finset (Fin n)) :=
  (vectors D q).map SparseCardinalRounding.selected

theorem integral (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1)
    (a : Fin (vectors D q).length) : ∀ i, point (vectors D q).states[a.val] i=0 ∨
      point (vectors D q).states[a.val] i=1 :=
  (SparseWeightedRounding.round_invariants (fun _ => 1) (fun _ => by norm_num)
    (initial D q) (initial_unit D hq) (show (0:ℚ) ≤ 1 by norm_num) (fun _ => le_rfl) a).1

theorem mean (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1) (i : Fin n) :
    (law D q).moment (fun S => if i∈S then 1 else 0)=if i∈D then q else 0 := by
  rw [law,SparseIntegerLaw.map_moment]
  calc
    _ = (vectors D q).moment (fun p => point p i) :=
      SparseIntegerLaw.moment_congr _ _ _ (fun a =>
        SparseCardinalRounding.selected_indicator _ (integral D hq a) i)
    _ = point (initial D q) i := SparseWeightedRounding.round_mean _ _ _ _
    _ = _ := point_initial D q i

theorem positive (D : Finset (Fin n)) (q : ℚ) (a : Fin (law D q).length) :
    0 < (law D q).law.rational.weight a := by
  exact ((SparseWeightedPartial.run (fun _ => 1) (fun _ => by norm_num) (initial D q) n).branch
    RationalLastFraction.probability RationalLastFraction.probability_unit
    RationalLastFraction.endpoint).compressAuto_positive SparseWeightedPartial.features a

theorem subset (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1)
    (a : Fin (law D q).length) : (law D q).states[a.val] ⊆ D := by
  intro i hi
  by_contra hn
  exact (law D q).zero_indicator (fun S => i∈S)
    (by rw [mean D hq i,ite_eq_right hn]) a (positive D q a) hi

theorem fixed (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1)
    (a : Fin (law D q).length) :
    (q=0 → (law D q).states[a.val]=∅) ∧ (q=1 → (law D q).states[a.val]=D) := by
  constructor
  · intro hq0
    apply eq_empty_iff_forall_notMem.mpr
    intro i
    exact (law D q).zero_indicator (fun S => i∈S)
      (by rw [mean D hq i,hq0]; split_ifs <;> rfl) a (positive D q a)
  · intro hq1
    apply Subset.antisymm (subset D hq a)
    intro i hi
    exact (law D q).one_indicator (fun S => i∈S)
      (by rw [mean D hq i,ite_eq_left hi,hq1]) a (positive D q a)

theorem count_error (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1)
    (a : Fin (law D q).length) :
    |(((law D q).states[a.val]).card:ℚ)-(D.card:ℚ)*q| ≤ 1 := by
  have hh := (SparseWeightedRounding.round_invariants (fun _ => 1) (fun _ => by norm_num)
    (initial D q) (initial_unit D hq) (show (0:ℚ) ≤ 1 by norm_num) (fun _ => le_rfl) a).2
  simp only [one_mul] at hh
  have hsum : (∑ i, point (initial D q) i)=(D.card:ℚ)*q := by
    simp only [point_initial,sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul]
  have hcard : (((law D q).states[a.val]).card:ℚ)=
      ∑ i, point (vectors D q).states[a.val] i := by
    have he := SparseIntegerLaw.map_states (vectors D q) SparseCardinalRounding.selected a
    change (law D q).states[a.val]=_ at he
    rw [he]
    calc
      _ = ∑ i, if i∈SparseCardinalRounding.selected (vectors D q).states[a.val] then (1:ℚ) else 0 := by simp
      _ = _ := sum_congr rfl (fun i _ =>
        SparseCardinalRounding.selected_indicator _ (integral D hq a) i)
  rw [hcard]
  rwa [hsum] at hh

theorem length (D : Finset (Fin n)) (q : ℚ) : (law D q).length ≤ n+n*n+1 :=
  SparseWeightedRounding.round_length _ _ _

end MetricKMedian.SparseTargetSubset
end
end

end OAI
