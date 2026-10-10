import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSignedBudget
import OAI.Combinatorics.KMedian.Sparse.SparseGridRounding

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

abbrev law (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) : SparseIntegerLaw (State n m) :=
  SparseSignedPreparation.law D c (fraction q) (SparseGridRounding.fraction_unit q hq) hc

def activation (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (z : State n m) (e : Fin m) (i : Fin n) : ℚ :=
  (if i∈D e then (base q e:ℚ) else 0)+(if i∈z.2.1 e then 1 else 0)

theorem fraction_identity (q : Fin m → ℚ) (e : Fin m) :
    (base q e:ℚ)+point (fraction q) e=q e := by
  simp only [point,fraction,Vector.getElem_ofFn,add_sub_cancel]

theorem length (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) :
    (law D c q hc hq).length ≤ (m+m*m+1)*((n*m+(n*m)*(n*m)+1)*((m+1)^2+1)) :=
  SparseSignedPreparation.length _ _ _ _ _

theorem budget (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) :
    ∀ a : Fin (law D c q hc hq).length,
      SparseSignedPreparation.BudgetSpec D c (base q)
        ((∑ e,SparseSignedPreparation.signed D c e*q e)+3) (law D c q hc hq).states[a.val] := by
  have hh := SparseSignedPreparation.law_budget D c (base q) (fraction q)
    (SparseGridRounding.fraction_unit q hq) hc
  simpa only [fraction_identity] using hh

theorem nominal_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m) :
    (law D c q hc hq).moment (fun z => SparseSignedPreparation.nominalCount (base q) z e)=q e := by
  unfold SparseSignedPreparation.nominalCount
  rw [SparseIntegerLaw.moment_add,
    SparseIntegerLaw.moment_const,SparseSignedPreparation.nominal,fraction_identity]

theorem nominal_pair (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e f : Fin m) (hef : e≠f) :
    (law D c q hc hq).moment (fun z =>
      SparseSignedPreparation.nominalCount (base q) z e*SparseSignedPreparation.nominalCount (base q) z f) ≤ q e*q f := by
  have hh := SparseIntegerLaw.moment_affine_pair_le (law D c q hc hq)
    (fun z => SparseBernoulli.flag z.2.2 e) (fun z => SparseBernoulli.flag z.2.2 f)
    (base q e:ℚ) (base q f:ℚ) (point (fraction q) e) (point (fraction q) f)
    (SparseSignedPreparation.nominal _ _ _ _ _ e) (SparseSignedPreparation.nominal _ _ _ _ _ f)
    (SparseSignedPreparation.nominal_pair _ _ _ _ _ e f hef)
  simpa only [SparseSignedPreparation.nominalCount,fraction_identity] using hh

theorem activation_mean (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m) (i : Fin n) :
    (law D c q hc hq).moment (fun z => activation D q z e i)=if i∈D e then q e else 0 := by
  unfold activation
  rw [SparseIntegerLaw.moment_add,SparseIntegerLaw.moment_const,SparseSignedPreparation.target]
  by_cases hi : i∈D e
  · simp only [ite_eq_left hi,fraction_identity]
  · simp only [ite_eq_right hi,add_zero]

theorem activation_pair (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (law D c q hc hq).moment (fun z => activation D q z e i*activation D q z f j) ≤
      (if i∈D e then q e else 0)*(if j∈D f then q f else 0) := by
  have hh := SparseIntegerLaw.moment_affine_pair_le (law D c q hc hq)
    (fun z => if i∈z.2.1 e then 1 else 0) (fun z => if j∈z.2.1 f then 1 else 0)
    (if i∈D e then (base q e:ℚ) else 0) (if j∈D f then (base q f:ℚ) else 0)
    (if i∈D e then point (fraction q) e else 0) (if j∈D f then point (fraction q) f else 0)
    (SparseSignedPreparation.target _ _ _ _ _ e i) (SparseSignedPreparation.target _ _ _ _ _ f j)
    (SparseSignedPreparation.target_pair _ _ _ _ _ e f hef i j)
  change (law D c q hc hq).moment (fun z => activation D q z e i*activation D q z f j) ≤ _ at hh
  by_cases hi : i∈D e <;> by_cases hj : j∈D f
  all_goals simpa only [hi,hj,ite_true,ite_false,fraction_identity,zero_add] using hh

theorem activation_adjacent (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (a : Fin (law D c q hc hq).length) (e : Fin m) (i : Fin n) :
    let b : ℚ := if i∈D e then (base q e:ℚ) else 0
    activation D q (law D c q hc hq).states[a.val] e i=b ∨
      activation D q (law D c q hc hq).states[a.val] e i=b+1 := by
  dsimp only [activation]
  split_ifs
  all_goals first | exact Or.inl (add_zero _) | exact Or.inr rfl

end MetricKMedian.SparseOuterLaw
end
end

end OAI
