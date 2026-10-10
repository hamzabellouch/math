import Mathlib
import OAI.Combinatorics.KMedian.Rounding.GridClipping
import OAI.Combinatorics.KMedian.Rounding.RationalRetain
import OAI.Combinatorics.KMedian.Sparse.SparseOuterCounts
import OAI.Combinatorics.KMedian.Sparse.SparseRescaledInner

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

def requests (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) : Fin n → Fin m → ℕ :=
  fun j => RationalRetain.keep (fun e => activationCount D q z e j) (Δ/2)

def total (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) : Fin n → ℕ :=
  fun j => Δ-min (∑ e,activationCount D q z e j) (Δ/2)

theorem requests_le (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) (e : Fin m) :
    requests D q Δ z j e ≤ activationCount D q z e j := RationalRetain.le _ _ _

theorem exact_total (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) :
    total D q Δ z j+(∑ e,requests D q Δ z j e)=Δ := by
  unfold total requests
  rw [RationalRetain.total]
  exact Nat.sub_add_cancel ((min_le_right _ _).trans (Nat.div_le_self _ _))

theorem total_le (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) : total D q Δ z j ≤ Δ := Nat.sub_le _ _

theorem total_half (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) {g : ℝ} (hg : 0 < g) (heven : Even Δ)
    (hunit : g*(Δ:ℝ)=1) : (1/2:ℝ) ≤ g*(total D q Δ z j:ℝ) :=
  (Preparation.grid_clip hg heven hunit (∑ e,activationCount D q z e j)).2.2.1

def kernel (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ) (z : State n m) :
    SparseIntegerLaw (State n m × SparseCounts.Table f n) :=
  (SparseRescaledInner.law P y p (total D q Δ z)).map (fun G => (z,G))

def law (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) :
    SparseIntegerLaw (State n m × SparseCounts.Table f n) :=
  (SparseOuterLaw.law D c q hc hq).bindIndexed
    (fun a => kernel D q Δ P y p (SparseOuterLaw.law D c q hc hq).states[a.val])

theorem length (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) :
    (law D c q Δ P y p hc hq).length ≤
      ((m+m*m+1)*((n*m+(n*m)*(n*m)+1)*((m+1)^2+1)))*(f*n+(f*n)*(f*n)+1) := by
  apply (SparseIntegerLaw.bindIndexed_length _ _ (f*n+(f*n)*(f*n)+1) ?_).trans
    (Nat.mul_le_mul_right _ (SparseOuterLaw.length D c q hc hq))
  intro a
  exact SparseBundles.length _

def Spec (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (zG : State n m × SparseCounts.Table f n) : Prop :=
  (∀ e,outsideCount q zG.1 e ≤ Δ) ∧
  (∀ j e,requests D q Δ zG.1 j e ≤ outsideCount q zG.1 e) ∧
  (∀ j e,j∉D e → requests D q Δ zG.1 j e=0) ∧
  (∀ j,(∑ i,zG.2 j i)=total D q Δ zG.1 j ∧
    (∀ i,zG.2 j i ≤ Δ) ∧ (∀ i,i∉P j → zG.2 j i=0))

theorem physical (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) (hqcap : ∀ e,q e ≤ Δ)
    (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j) (hm : ∀ j,∑ i∈P j,y i=p j) :
    ∀ a : Fin (law D c q Δ P y p hc hq).length,
      Spec D q Δ P (law D c q Δ P y p hc hq).states[a.val] := by
  unfold law
  apply SparseIntegerLaw.bindIndexed_property _ _ (Spec D q Δ P)
  intro a
  unfold kernel
  intro b
  rw [SparseIntegerLaw.map_states]
  refine ⟨fun e => outsideCount_le D c q hc hq Δ hqcap a e,?_,?_,?_⟩
  · intro j e
    exact (requests_le D q Δ _ j e).trans (activationCount_le D c q hc hq a e j)
  · intro j e hj
    have hh := requests_le D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j e
    rw [activationCount_support D c q hc hq a e j hj] at hh
    exact Nat.eq_zero_of_le_zero hh
  · intro j
    exact SparseRescaledInner.invariants P y p _ Δ hy hp hm
      (total_le D q Δ _) b j

end MetricKMedian.SparsePrepared
end
end

end OAI
