import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseMap
import OAI.Combinatorics.KMedian.Sparse.SparseGraphRun
import OAI.Combinatorics.KMedian.Sparse.SparseCardinalRounding
import OAI.Combinatorics.KMedian.Sparse.SparseSupport

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

def columns (q : Fin n → Fin m → ℚ) (i : Fin m) : SparseIntegerLaw (Finset (Fin n)) :=
  (SparseCardinalRounding.round (Vector.ofFn (fun h => q h i))).map SparseCardinalRounding.selected

theorem columns_moment (q : Fin n → Fin m → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1) (hs : ∀ i, (∑ h, q h i)=(Δ:ℚ))
    (h : Fin n) (i : Fin m) : (columns q i).moment (fun S => if h∈S then 1 else 0)=q h i := by
  rw [columns,SparseIntegerLaw.map_moment]
  calc
    _ = (SparseCardinalRounding.round (Vector.ofFn (fun h => q h i))).moment
        (fun p => RationalWeightedStep.point p h) := by
      apply SparseIntegerLaw.moment_congr
      intro a
      have hh := SparseCardinalRounding.round_invariants (Vector.ofFn (fun h => q h i))
        (fun h => by simpa only [RationalWeightedStep.point,Vector.getElem_ofFn] using hq h i)
        Δ (by simpa only [RationalWeightedStep.point,Vector.getElem_ofFn] using hs i) a
      exact SparseCardinalRounding.selected_indicator _ hh.1 h
    _ = _ := by rw [SparseCardinalRounding.round_mean]; simp only [RationalWeightedStep.point,Vector.getElem_ofFn]

theorem columns_card (q : Fin n → Fin m → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1) (hs : ∀ i, (∑ h, q h i)=(Δ:ℚ))
    (i : Fin m) (a : Fin (columns q i).length) : ((columns q i).states[a.val]).card=Δ := by
  change Fin (SparseCardinalRounding.round (Vector.ofFn (fun h => q h i))).length at a
  have he := SparseIntegerLaw.map_states (SparseCardinalRounding.round
    (Vector.ofFn (fun h => q h i))) SparseCardinalRounding.selected a
  change (columns q i).states[a.val]=_ at he
  rw [he]
  have hh := SparseCardinalRounding.round_invariants (Vector.ofFn (fun h => q h i))
    (fun h => by simpa only [RationalWeightedStep.point,Vector.getElem_ofFn] using hq h i)
    Δ (by simpa only [RationalWeightedStep.point,Vector.getElem_ofFn] using hs i) a
  exact SparseCardinalRounding.selected_card _ hh.1 Δ hh.2

def law (q : Fin n → Fin m → ℚ) : SparseIntegerLaw (Graph n m) := run (columns q) m

theorem law_spec (q : Fin n → Fin m → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1) (hs : ∀ i, (∑ h, q h i)=(Δ:ℚ)) :
    (law q).length ≤ n*m+(n*m)*(n*m)+1 ∧
    (∀ a : Fin (law q).length, ∀ i, ((law q).states[a.val] i).card=Δ) ∧
    (∀ h i, (law q).moment (fun G => edge G h i)=q h i) ∧
    (∀ h l i j, i≠j → (law q).moment (fun G => edge G h i*edge G l j)=q h i*q l j) := by
  refine ⟨run_length (columns q) m,?_,?_,?_⟩
  · intro a i
    exact run_columns (columns q) (fun _ S => S.card=Δ) (columns_card q Δ hq hs) m
      (le_refl m) a i i.isLt
  · intro h i
    have hh := run_single (columns q) q (columns_moment q Δ hq hs) m (le_refl m) h i
    simpa only [law,target,i.isLt,ite_eq_left] using hh
  · intro h l i j hij
    have hh := run_pair (columns q) q (columns_moment q Δ hq hs) m (le_refl m) h l i j hij
    simpa only [law,target,i.isLt,j.isLt,ite_eq_left] using hh

theorem run_positive (ν : Fin m → SparseIntegerLaw (Finset (Fin n))) (t : ℕ) :
    ∀ a : Fin (run ν t).length, 0 < (run ν t).law.rational.weight a := by
  induction t with
  | zero => intro a; change 0 < ((1:ℤ):ℚ)/1; norm_num
  | succ t ih =>
    let inv : SparseIntegerLaw (Graph n m) → Prop := fun μ =>
      ∀ a : Fin μ.length, 0 < μ.law.rational.weight a
    change inv (run ν (t+1))
    by_cases ht : t < m
    · rw [run,dite_eq_left ht]
      intro a
      exact ((run ν t).prod (ν ⟨t,ht⟩) (fun G S => next G S ⟨t,ht⟩)).compressAuto_positive features a
    · rw [run,dite_eq_right ht]
      exact ih

theorem law_fixed (q : Fin n → Fin m → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1) (hs : ∀ i, (∑ h, q h i)=(Δ:ℚ))
    (a : Fin (law q).length) (h : Fin n) (i : Fin m) :
    (q h i=1 → h∈(law q).states[a.val] i) ∧
    (q h i=0 → h∉(law q).states[a.val] i) := by
  have hh := (law_spec q Δ hq hs).2.2.1 h i
  have hp := run_positive (columns q) m a
  constructor
  · intro he
    exact (law q).one_indicator (fun G => h∈G i) (hh.trans he) a hp
  · intro he
    exact (law q).zero_indicator (fun G => h∈G i) (hh.trans he) a hp

end MetricKMedian.SparseGraph
end
end

end OAI
