import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSignedFixed
import OAI.Combinatorics.KMedian.Sparse.SparseOuterLaw

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem point_fixed (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m)
    (he : point (fraction q) e=0) : ∀ a : Fin (law D c q hc hq).length,
      point (law D c q hc hq).states[a.val].1 e=0 := by
  unfold law SparseSignedPreparation.law
  dsimp only
  apply SparseIntegerLaw.bindIndexed_property _ _ (fun z : State n m => point z.1 e=0)
  intro a
  unfold SparseSignedPreparation.kernel
  apply SparseIntegerLaw.prod_property _ _ _ (fun z : State n m => point z.1 e=0)
  intro b d
  exact (SparseSignedRounding.fixed (SparseSignedPreparation.signed D c) (fraction q)
    (SparseGridRounding.fraction_unit q hq)
    (fun j _ => (sub_le_self _ (Nat.cast_nonneg _)).trans (hc j).2) e (Or.inl he) a).trans he

def outsideCount (q : Fin m → ℚ) (z : State n m) (e : Fin m) : ℕ :=
  base q e+if 0 < point z.1 e then 1 else 0

def activationCount (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (z : State n m) (e : Fin m) (i : Fin n) : ℕ :=
  (if i∈D e then base q e else 0)+(if i∈z.2.1 e then 1 else 0)

theorem outsideCount_cast (q : Fin m → ℚ) (z : State n m) (e : Fin m) :
    (outsideCount q z e:ℚ)=SparseSignedPreparation.outside (base q) z e := by
  simp only [outsideCount,SparseSignedPreparation.outside,SparseStarActivation.upper]
  split_ifs <;> simp

theorem activationCount_cast (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (z : State n m) (e : Fin m) (i : Fin n) :
    (activationCount D q z e i:ℚ)=activation D q z e i := by
  simp only [activationCount,activation,Nat.cast_add,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]

theorem outsideCount_le (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (L : ℕ)
    (hL : ∀ e,q e ≤ L) (a : Fin (law D c q hc hq).length) (e : Fin m) :
    outsideCount q (law D c q hc hq).states[a.val] e ≤ L := by
  have hb : base q e ≤ L := by exact_mod_cast (Nat.floor_le (hq e)).trans (hL e)
  by_cases hi : 0 < point (law D c q hc hq).states[a.val].1 e
  · have hl : base q e < L := by
      by_contra hn
      have heq : base q e=L := le_antisymm hb (le_of_not_gt hn)
      have hz : point (fraction q) e=0 := by
        simp only [fraction,point,Vector.getElem_ofFn]
        have hh := Nat.floor_le (hq e)
        change (base q e:ℚ) ≤ q e at hh
        have hh' := hL e
        rw [heq] at hh ⊢
        linarith only [hh,hh']
      have hf := point_fixed D c q hc hq e hz a
      rw [hf] at hi
      exact (lt_irrefl 0) hi
    simpa only [outsideCount,ite_eq_left hi] using Nat.add_one_le_iff.mpr hl
  · simpa only [outsideCount,ite_eq_right hi,Nat.add_zero] using hb

theorem activationCount_support (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (a : Fin (law D c q hc hq).length) (e : Fin m) (i : Fin n) (hi : i∉D e) :
    activationCount D q (law D c q hc hq).states[a.val] e i=0 := by
  have hh : i∉(law D c q hc hq).states[a.val].2.1 e := fun hh => hi ((budget D c q hc hq a).1 e hh)
  simp only [activationCount,ite_eq_right hi,ite_eq_right hh,Nat.add_zero]

theorem activationCount_le (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (a : Fin (law D c q hc hq).length) (e : Fin m) (i : Fin n) :
    activationCount D q (law D c q hc hq).states[a.val] e i ≤
      outsideCount q (law D c q hc hq).states[a.val] e := by
  by_cases hi : i∈D e
  · have hh := (budget D c q hc hq a).2.2.2.2.1 e i
    have he : (activationCount D q (law D c q hc hq).states[a.val] e i:ℚ) ≤
        (outsideCount q (law D c q hc hq).states[a.val] e:ℚ) := by
      rw [activationCount_cast,outsideCount_cast]
      simpa only [activation,ite_eq_left hi] using hh
    exact_mod_cast he
  · rw [activationCount_support D c q hc hq a e i hi]
    exact Nat.zero_le _

end MetricKMedian.SparseOuterLaw
end
end

end OAI
