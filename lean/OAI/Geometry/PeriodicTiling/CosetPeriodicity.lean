import OAI.Geometry.PeriodicTiling.TilingBasic
import OAI.Geometry.PeriodicTiling.ScalarPolynomialPeriodicity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace PeriodicTilingThree

theorem coset_configuration_has_period {m : ℕ}
    (P : Fin m → ℤ → ℝ) (b : Fin m → ℤ) (a : Plane → ℝ)
    (hzero : ∀ j n, 0 ≤ P j n)
    (hpair : ∀ i j, i ≠ j → ∀ n r, P i n + P j r ≤ 1)
    (hsum : ∀ x : Plane, a x = 1 - ∑ j, P j (x.1 + b j * x.2))
    (degree : ℕ) (hdegree : 0 < degree)
    (hpoly : ∀ j, (forwardDiff^[degree])
      (fun n => (P j n : AddCircle (1 : ℝ))) = 0) :
    ∃ v : Plane, v ≠ 0 ∧ Function.Periodic a v := by
  classical
  by_cases hbounded : ∀ j, ∃ c : ℝ, c < 1 ∧ ∀ n, P j n ≤ c
  · have hp : ∀ j, ∃ q : ℕ, 0 < q ∧ Function.Periodic (P j) (q : ℤ) := by
      intro j
      obtain ⟨c, hc, hPc⟩ := hbounded j
      exact real_polynomial_periodic_of_bounded_lt_one degree hdegree
        (P j) c (hzero j) hPc hc (hpoly j)
    choose p hp hperiod using hp
    let Q : ℕ := ∏ j, p j
    have hQ : 0 < Q := Finset.prod_pos fun j _ => hp j
    refine ⟨(0, (Q : ℤ)), ?_, ?_⟩
    · intro h
      have hz : (Q : ℤ) = 0 := congrArg Prod.snd h
      exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hQ)) hz
    · intro x
      rw [hsum, hsum]
      apply congrArg (fun y : ℝ => 1 - y)
      apply Finset.sum_congr rfl
      intro j _hj
      have hd : p j ∣ Q := Finset.dvd_prod_of_mem p (Finset.mem_univ j)
      obtain ⟨k, hk⟩ := hd
      have hperiodQ : Function.Periodic (P j) (b j * (Q : ℤ)) := by
        simpa only [hk, Nat.cast_mul, Int.cast_id, mul_assoc, mul_left_comm, mul_comm] using
          (hperiod j).int_mul (b j * (k : ℤ))
      change P j (x.1 + 0 + b j * (x.2 + (Q : ℤ))) =
        P j (x.1 + b j * x.2)
      rw [show x.1 + 0 + b j * (x.2 + (Q : ℤ)) =
        (x.1 + b j * x.2) + b j * (Q : ℤ) by ring]
      exact hperiodQ _
  · obtain ⟨j, hj⟩ := not_forall.mp hbounded
    have hother : ∀ i, i ≠ j → ∀ n, P i n = 0 := by
      intro i hij n
      apply le_antisymm _ (hzero i n)
      apply le_of_not_gt
      intro hpos
      apply hj
      refine ⟨1 - P i n, by linarith, ?_⟩
      intro r
      have hcross := hpair j i (Ne.symm hij) r n
      linarith
    have hone : ∀ x : Plane, a x = 1 - P j (x.1 + b j * x.2) := by
      intro x
      rw [hsum]
      apply congrArg (fun y : ℝ => 1 - y)
      apply Finset.sum_eq_single j
      · intro i _hi hij
        exact hother i hij _
      · intro hj'
        exact (hj' (Finset.mem_univ j)).elim
    refine ⟨(-b j, 1), ?_, ?_⟩
    · intro h
      have hz : (1 : ℤ) = 0 := congrArg Prod.snd h
      exact one_ne_zero hz
    · intro x
      rw [hone, hone]
      apply congrArg (fun n : ℤ => 1 - P j n)
      change x.1 + -b j + b j * (x.2 + 1) = x.1 + b j * x.2
      ring

end PeriodicTilingThree

end OAI
