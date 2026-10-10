import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSignedRounding
import OAI.Combinatorics.KMedian.Sparse.SparseStarActivation

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

abbrev State (n m : ℕ) := Vector ℚ m × ((Fin m → Finset (Fin n)) × (Fin m → Bool))

def kernel (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) : SparseIntegerLaw (State n m) :=
  (SparseStarActivation.law D (point q)).prod
    (SparseBernoulli.run (d := 2) (point q) hq m) (fun S ω => (q,S,ω))

def signed (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) : Fin m → ℚ :=
  fun e => c e-((D e).card:ℚ)

def law (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) :
    SparseIntegerLaw (State n m) :=
  let μ := SparseSignedRounding.round (signed D c) p hp
  μ.bindIndexed (fun a => kernel D μ.states[a.val]
    (SparseSignedRounding.round_invariants (signed D c) p hp (fun e _ =>
      (sub_le_self _ (Nat.cast_nonneg _)).trans (hc e).2) a).1)

theorem kernel_nominal (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) (e : Fin m) :
    (kernel D q hq).moment (fun z => SparseBernoulli.flag z.2.2 e)=point q e := by
  rw [kernel,SparseIntegerLaw.prod_moment]
  simp only [SparseBernoulli.single_moment,SparseIntegerLaw.moment_const]

theorem kernel_nominal_pair (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) (e f : Fin m) (hef : e≠f) :
    (kernel D q hq).moment (fun z => SparseBernoulli.flag z.2.2 e*SparseBernoulli.flag z.2.2 f)=
      point q e*point q f := by
  rw [kernel,SparseIntegerLaw.prod_moment]
  simp only [SparseBernoulli.pair_moment _ _ _ _ hef,SparseIntegerLaw.moment_const]

theorem kernel_target (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) (e : Fin m) (i : Fin n) :
    (kernel D q hq).moment (fun z => if i∈z.2.1 e then 1 else 0)=
      if i∈D e then point q e else 0 := by
  rw [kernel,SparseIntegerLaw.prod_moment]
  apply Eq.trans ?_ (SparseStarActivation.mean D (point q) hq e i)
  apply SparseIntegerLaw.moment_congr
  intro a
  dsimp only
  by_cases hi : i∈(SparseStarActivation.law D (point q)).states[a.val] e
  all_goals simp only [hi,ite_true,ite_false]; exact SparseIntegerLaw.moment_const _ _

theorem kernel_target_pair (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (kernel D q hq).moment (fun z => (if i∈z.2.1 e then 1 else 0)*(if j∈z.2.1 f then 1 else 0))=
      (if i∈D e then point q e else 0)*(if j∈D f then point q f else 0) := by
  rw [kernel,SparseIntegerLaw.prod_moment]
  apply Eq.trans ?_ (SparseStarActivation.pair D (point q) hq e f hef i j)
  apply SparseIntegerLaw.moment_congr
  intro a
  dsimp only
  by_cases hi : i∈(SparseStarActivation.law D (point q)).states[a.val] e <;>
    by_cases hj : j∈(SparseStarActivation.law D (point q)).states[a.val] f
  all_goals simp only [hi,hj,ite_true,ite_false]; exact SparseIntegerLaw.moment_const _ _

theorem nominal (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (e : Fin m) :
    (law D c p hp hc).moment (fun z => SparseBernoulli.flag z.2.2 e)=point p e := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_nominal]
  exact SparseSignedRounding.round_mean _ _ _ _

theorem nominal_pair (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1)
    (e f : Fin m) (hef : e≠f) :
    (law D c p hp hc).moment (fun z => SparseBernoulli.flag z.2.2 e*SparseBernoulli.flag z.2.2 f) ≤
      point p e*point p f := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_nominal_pair _ _ _ _ _ hef]
  exact SparseSignedRounding.round_pair _ _ _ _ _ hef

theorem target (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1)
    (e : Fin m) (i : Fin n) :
    (law D c p hp hc).moment (fun z => if i∈z.2.1 e then 1 else 0)=
      if i∈D e then point p e else 0 := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_target]
  by_cases hi : i∈D e
  · simp only [ite_eq_left hi]
    exact SparseSignedRounding.round_mean _ _ _ _
  · simp only [ite_eq_right hi,mul_zero,sum_const_zero]

theorem target_pair (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1)
    (e f : Fin m) (hef : e≠f) (i j : Fin n) :
    (law D c p hp hc).moment (fun z => (if i∈z.2.1 e then 1 else 0)*(if j∈z.2.1 f then 1 else 0)) ≤
      (if i∈D e then point p e else 0)*(if j∈D f then point p f else 0) := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_target_pair _ _ _ _ _ hef]
  by_cases hi : i∈D e <;> by_cases hj : j∈D f
  · simp only [ite_eq_left hi,ite_eq_left hj]
    exact SparseSignedRounding.round_pair _ _ _ _ _ hef
  all_goals simp only [hi,hj,ite_true,ite_false,mul_zero,zero_mul,sum_const_zero,le_refl]

theorem length (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) :
    (law D c p hp hc).length ≤ (m+m*m+1)*((n*m+(n*m)*(n*m)+1)*((m+1)^2+1)) := by
  unfold law
  apply le_trans (SparseIntegerLaw.bindIndexed_length _ _ _ ?_)
    (Nat.mul_le_mul_right _ (SparseSignedRounding.round_length _ _ _))
  intro a
  exact Nat.mul_le_mul (SparseStarActivation.length D _)
    (SparseBernoulli.run_length (d := 2) _ _ _)

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
