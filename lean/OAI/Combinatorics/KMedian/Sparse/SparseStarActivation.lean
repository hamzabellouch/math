import Mathlib
import OAI.Combinatorics.KMedian.Rounding.ExceptionalStar
import OAI.Combinatorics.KMedian.Sparse.SparseGraphRun
import OAI.Combinatorics.KMedian.Sparse.SparseTargetSubset

namespace OAI

section
section
namespace MetricKMedian.SparseStarActivation
open Finset
variable {n m : ℕ}

def law (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) :
    SparseIntegerLaw (Fin m → Finset (Fin n)) :=
  SparseGraph.run (fun e => SparseTargetSubset.law (D e) (q e)) m

def upper (q : ℚ) : ℚ := if 0 < q then 1 else 0

theorem mean (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (e : Fin m) (i : Fin n) :
    (law D q).moment (fun S => if i∈S e then 1 else 0)=if i∈D e then q e else 0 := by
  have hh := SparseGraph.run_single (fun e => SparseTargetSubset.law (D e) (q e))
    (fun i e => if i∈D e then q e else 0) (fun i e => SparseTargetSubset.mean (D e) (hq e) i)
    m (le_refl m) i e
  simpa only [law,SparseGraph.edge,SparseGraph.target,e.isLt,ite_eq_left] using hh

theorem pair (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (law D q).moment (fun S => (if i∈S e then 1 else 0)*(if j∈S f then 1 else 0))=
      (if i∈D e then q e else 0)*(if j∈D f then q f else 0) := by
  have hh := SparseGraph.run_pair (fun e => SparseTargetSubset.law (D e) (q e))
    (fun i e => if i∈D e then q e else 0) (fun i e => SparseTargetSubset.mean (D e) (hq e) i)
    m (le_refl m) i j e f hef
  simpa only [law,SparseGraph.edge,SparseGraph.target,e.isLt,f.isLt,ite_eq_left] using hh

theorem columns (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (a : Fin (law D q).length) (e : Fin m) :
    let S := (law D q).states[a.val] e
    S ⊆ D e ∧ |(S.card:ℚ)-((D e).card:ℚ)*q e| ≤ 1 ∧
      (q e=0 → S=∅) ∧ (q e=1 → S=D e) := by
  apply SparseGraph.run_columns (fun e => SparseTargetSubset.law (D e) (q e))
    (fun e S => S ⊆ D e ∧ |(S.card:ℚ)-((D e).card:ℚ)*q e| ≤ 1 ∧
      (q e=0 → S=∅) ∧ (q e=1 → S=D e))
    (fun e b => ⟨SparseTargetSubset.subset (D e) (hq e) b,
      SparseTargetSubset.count_error (D e) (hq e) b,
      SparseTargetSubset.fixed (D e) (hq e) b⟩) m (le_refl m) a e e.isLt

theorem upper_domination (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (a : Fin (law D q).length) (e : Fin m) (i : Fin n) :
    (if i∈(law D q).states[a.val] e then (1:ℚ) else 0) ≤ upper (q e) := by
  by_cases he : 0 < q e
  · simp only [upper,ite_eq_left he]
    split_ifs <;> norm_num
  · have hz : q e=0 := le_antisymm (le_of_not_gt he) (hq e).1
    rw [(columns D q hq a e).2.2.1 hz]
    simp only [notMem_empty,ite_false,upper,ite_eq_right he,le_refl]

theorem error (D : Fin m → Finset (Fin n)) (q c : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1)
    (hsmall : (univ.filter (fun e => 0 < q e ∧ q e < 1)).card ≤ 1)
    (a : Fin (law D q).length) :
    (∑ e, (c e*(upper (q e)-q e)+((D e).card:ℚ)*q e-
      (((law D q).states[a.val] e).card:ℚ))) ≤ 2 := by
  have hq0 : ∀ e, (0:ℝ) ≤ (q e:ℝ) := fun e => by exact_mod_cast (hq e).1
  have hq1 : ∀ e, (q e:ℝ) ≤ 1 := fun e => by exact_mod_cast (hq e).2
  have hc0 : ∀ e, (0:ℝ) ≤ (c e:ℝ) := fun e => by exact_mod_cast (hc e).1
  have hc1 : ∀ e, (c e:ℝ) ≤ 1 := fun e => by exact_mod_cast (hc e).2
  have hs : (MarginalRounding.fractional (fun e => (q e:ℝ))).card ≤ 1 := by
    unfold MarginalRounding.fractional
    have he : (univ.filter (fun e => 0 < (q e:ℝ) ∧ (q e:ℝ)<1))=
        univ.filter (fun e => 0 < q e ∧ q e<1) := by
      apply filter_congr
      intro e _
      norm_cast
    rwa [he]
  have hh := Preparation.exceptional_raw_error D (fun e => (q e:ℝ)) (fun e => (c e:ℝ))
    (law D q).states[a.val] hq0 hq1 hc0 hc1 hs (fun e => ⟨by
      exact_mod_cast (columns D q hq a e).2.1,
      fun he => (columns D q hq a e).2.2.1 (by exact_mod_cast he),
      fun he => (columns D q hq a e).2.2.2 (by exact_mod_cast he)⟩)
  have hu : ∀ e, Preparation.upperBit (q e:ℝ)=(upper (q e):ℝ) := by
    intro e
    simp only [Preparation.upperBit,upper]
    norm_cast
  simp_rw [hu] at hh
  exact_mod_cast hh

theorem length (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) :
    (law D q).length ≤ n*m+(n*m)*(n*m)+1 := SparseGraph.run_length _ _

end MetricKMedian.SparseStarActivation
end
end

end OAI
