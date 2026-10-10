import Mathlib

namespace OAI

section
section
namespace MetricKMedian.RationalRetain
open Finset

def keep : {n : ℕ} → (Fin n → ℕ) → ℕ → (Fin n → ℕ)
  | 0,_,_ => Fin.elim0
  | n+1,q,k => Fin.cons (min (q 0) k) (keep (fun i : Fin n => q i.succ) (k-min (q 0) k))

theorem le {n : ℕ} (q : Fin n → ℕ) (k : ℕ) : ∀ i, keep q k i ≤ q i := by
  induction n generalizing k with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [keep,Fin.cons_zero] using min_le_left (q 0) k
    · simpa only [keep,Fin.cons_succ] using ih (fun j => q j.succ) (k-min (q 0) k) j

theorem zero {n : ℕ} (q : Fin n → ℕ) (k : ℕ) (i : Fin n) (hi : q i=0) :
    keep q k i=0 := Nat.eq_zero_of_le_zero (hi ▸ le q k i)

theorem total {n : ℕ} (q : Fin n → ℕ) (k : ℕ) :
    (∑ i,keep q k i)=min (∑ i,q i) k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [keep,Fin.cons_zero,Fin.cons_succ]
    rw [ih]
    omega

def retained {n t : ℕ} (q : Fin t → Fin n → ℕ) (Δ : ℕ) : Fin t → Fin n → ℕ :=
  fun j => keep (q j) (Δ/2)

theorem retained_le {n t : ℕ} (q : Fin t → Fin n → ℕ) (Δ : ℕ) (j : Fin t) (i : Fin n) :
    retained q Δ j i ≤ q j i := le _ _ _

theorem retained_total {n t : ℕ} (q : Fin t → Fin n → ℕ) (Δ : ℕ) (j : Fin t) :
    (∑ i,retained q Δ j i)=min (∑ i,q j i) (Δ/2) := total _ _

end MetricKMedian.RationalRetain
end
end

end OAI
