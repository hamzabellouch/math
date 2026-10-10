import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.RingTheory.Nilpotent.Basic

namespace OAI

/-! # Nilpotent perturbations along a finite filtration

An operator which agrees with a nilpotent operator on each successive
quotient is nilpotent. No commutation of the two operators is required.
-/

namespace PolycyclicRecognition
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem nilpotent_of_raises_finite_filtration
    (F : ℕ → Submodule ℝ V) (hzero : F 0 = ⊤) {c : ℕ} (hc : F c = ⊥)
    (a : Module.End ℝ V) (ha : ∀ k x, x ∈ F k → a x ∈ F (k + 1)) :
    IsNilpotent a := by
  have hp (k : ℕ) (x : V) : (a ^ k) x ∈ F k := by
    induction k with
    | zero => rw [hzero]; trivial
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact ha k _ ih
  refine ⟨c, LinearMap.ext fun x => ?_⟩
  exact (Submodule.mem_bot ℝ).mp (hc ▸ hp c x)

theorem nilpotent_of_filtered_nilpotent_perturbation
    (F : ℕ → Submodule ℝ V) (hzero : F 0 = ⊤) {c : ℕ} (hc : F c = ⊥)
    (a b : Module.End ℝ V)
    (ha : ∀ k x, x ∈ F k → a x ∈ F k)
    (hb : ∀ k x, x ∈ F k → b x ∈ F k)
    (hdiff : ∀ k x, x ∈ F k → (a - b) x ∈ F (k + 1))
    (hbn : IsNilpotent b) : IsNilpotent a := by
  have hbp (n k : ℕ) (x : V) (hx : x ∈ F k) : (b ^ n) x ∈ F k := by
    induction n with
    | zero => exact hx
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hb k _ ih
  have hp (n k : ℕ) (x : V) (hx : x ∈ F k) :
      (a ^ n) x - (b ^ n) x ∈ F (k + 1) := by
    induction n with
    | zero => simp only [pow_zero, Module.End.one_apply, sub_self, Submodule.zero_mem]
    | succ n ih =>
      have hh := (F (k + 1)).add_mem (ha (k + 1) _ ih) (hdiff k _ (hbp n k x hx))
      convert hh using 1; simp only [pow_succ', Module.End.mul_apply,
        LinearMap.sub_apply, map_sub]; abel
  obtain ⟨m, hm⟩ := hbn
  have hraise (k : ℕ) (x : V) (hx : x ∈ F k) : (a ^ m) x ∈ F (k + 1) := by
    simpa only [hm, LinearMap.zero_apply, sub_zero] using hp m k x hx
  obtain ⟨n, hn⟩ := nilpotent_of_raises_finite_filtration F hzero hc (a ^ m) hraise
  exact ⟨m * n, by rwa [pow_mul]⟩

end PolycyclicRecognition

end OAI
