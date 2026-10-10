import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel

namespace OAI

/-! # Polynomial annihilators under a filtration-raising perturbation

If `D` preserves a finite descending filtration and `N` raises its level,
then a polynomial annihilating `D`, evaluated at `D + N`, raises its level.
Consequently a power of that polynomial annihilates `D + N`.
-/

noncomputable section
namespace PolycyclicRecognition

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (B : ℕ → Submodule ℝ V) (D N : Module.End ℝ V)
  (hB : Antitone B)
  (hD : ∀ k v, v ∈ B k → D v ∈ B k)
  (hN : ∀ k v, v ∈ B k → N v ∈ B (k + 1))

include hB hD hN

theorem filtered_sum_maps (k : ℕ) (v : V) (hv : v ∈ B k) : (D + N) v ∈ B k := by
  exact (B k).add_mem (hD k v hv) (hB (Nat.le_succ k) (hN k v hv))

theorem filtered_sum_pow_maps (a k : ℕ) (v : V) (hv : v ∈ B k) :
    ((D + N) ^ a) v ∈ B k := by
  induction a with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hv
  | succ a ha =>
    rw [pow_succ', Module.End.mul_apply]
    exact filtered_sum_maps B D N hB hD hN k _ ha

theorem filtered_pow_difference (a k : ℕ) (v : V) (hv : v ∈ B k) :
    ((D + N) ^ a) v - (D ^ a) v ∈ B (k + 1) := by
  induction a with
  | zero => simpa only [pow_zero, sub_self] using (B (k + 1)).zero_mem
  | succ a ha =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.add_apply]
    have heq : D (((D + N) ^ a) v) + N (((D + N) ^ a) v) - D ((D ^ a) v) =
        D (((D + N) ^ a) v - (D ^ a) v) + N (((D + N) ^ a) v) := by
      rw [map_sub]
      abel
    rw [heq]
    exact (B (k + 1)).add_mem (hD _ _ ha)
      (hN _ _ (filtered_sum_pow_maps B D N hB hD hN a k v hv))

theorem filtered_polynomial_difference (p : ℝ[X]) (k : ℕ) (v : V) (hv : v ∈ B k) :
    aeval (D + N) p v - aeval D p v ∈ B (k + 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply]
    have heq : aeval (D + N) p v + aeval (D + N) q v -
        (aeval D p v + aeval D q v) =
        (aeval (D + N) p v - aeval D p v) + (aeval (D + N) q v - aeval D q v) := by abel
    rw [heq]
    exact (B (k + 1)).add_mem hp hq
  | monomial a r =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    rw [← smul_sub]
    exact (B (k + 1)).smul_mem r (filtered_pow_difference B D N hB hD hN a k v hv)

theorem filtered_polynomial_annihilator (c : ℕ) (hzero : B 0 = ⊤) (hc : B c = ⊥)
    (p : ℝ[X]) (hp : aeval D p = 0) : aeval (D + N) (p ^ c) = 0 := by
  have hraise (k : ℕ) (v : V) (hv : v ∈ B k) : aeval (D + N) p v ∈ B (k + 1) := by
    simpa only [hp, LinearMap.zero_apply, sub_zero] using
      filtered_polynomial_difference B D N hB hD hN p k v hv
  have hpow (k : ℕ) (v : V) : ((aeval (D + N) p) ^ k) v ∈ B k := by
    induction k with
    | zero => rw [hzero]; trivial
    | succ k hk =>
      rw [pow_succ', Module.End.mul_apply]
      exact hraise k _ hk
  rw [map_pow]
  ext v
  have h := hpow c v
  rw [hc, Submodule.mem_bot] at h
  exact h

end PolycyclicRecognition

end

end OAI
