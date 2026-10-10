import OAI.NumberTheory.Ostmann.Construction.IntegerIntervalDistribution

namespace OAI

/-! # A positive periodic sum over a finite interval -/

namespace Ostmann

open scoped BigOperators

theorem periodic_residue_sum_le (q W : ℕ) [NeZero q]
    (F : ZMod q → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ n ∈ Finset.Ioc 0 W, F (n : ZMod q)) ≤
      ((W : ℝ) / q + 1) * ∑ x : ZMod q, F x := by
  classical
  have hmaps (n : ℕ) (_ : n ∈ Finset.Ioc 0 W) :
      (n : ZMod q) ∈ (Finset.univ : Finset (ZMod q)) := Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  have heq : ((Finset.Ioc 0 W).filter (fun n : ℕ => (n : ZMod q) = x)) =
      (Finset.Ioc 0 W).filter (fun n => Nat.ModEq q n x.val) := by
    ext n
    have hc : (n : ZMod q) = x ↔ Nat.ModEq q n x.val := by
      calc
        _ ↔ (n : ZMod q) = (x.val : ZMod q) := by rw [ZMod.natCast_zmod_val]
        _ ↔ _ := ZMod.natCast_eq_natCast_iff n x.val q
    simp only [Finset.mem_filter, hc]
  have hb := integer_interval_residue_error 0 W q x.val (Nat.zero_le _)
    (Nat.pos_of_ne_zero (NeZero.ne q))
  have hcard : (((Finset.Ioc 0 W).filter (fun n : ℕ => (n : ZMod q) = x)).card : ℝ) ≤
      (W : ℝ) / q + 1 := by
    rw [heq]
    have hh := (abs_le.mp hb).2
    simp only [Nat.cast_zero, sub_zero] at hh
    linarith
  calc
    _ = (((Finset.Ioc 0 W).filter (fun n : ℕ => (n : ZMod q) = x)).card : ℝ) * F x := by
      calc
        _ = ∑ _n ∈ (Finset.Ioc 0 W).filter (fun n : ℕ => (n : ZMod q) = x), F x := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [(Finset.mem_filter.mp hn).2]
        _ = _ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (hF x)

end Ostmann

end OAI
