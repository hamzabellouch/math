import OAI.NumberTheory.Ostmann.Preliminaries.PrimeSums
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisionAlgebra

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Preliminaries
open scoped BigOperators

theorem weighted_root_collision_lower (U V : Finset ℕ)
    (hU : U.Nonempty) (hV : V.Nonempty) (Q : ℕ)
    (P : Finset ℕ) (hP : P ⊆ Q.primesLE)
    (hsplit : ∀ p ∈ P, 4/(p:ℝ) ≤ rootCollisionProbability U p+rootCollisionProbability V p) :
    2*(∑ p ∈ Q.primesLE,Real.log (p:ℝ)/p)+2*(∑ p ∈ P,Real.log (p:ℝ)/p) ≤
      ∑ p ∈ Q.primesLE,Real.log (p:ℝ)*(rootCollisionProbability U p+rootCollisionProbability V p) := by
  classical
  have hfilter : Q.primesLE.filter (fun p => p∈P)=P := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hP h,h⟩⟩
  have hsum : (∑ p ∈ P,Real.log (p:ℝ)/p) =
      ∑ p ∈ Q.primesLE, if p∈P then Real.log (p:ℝ)/p else 0 := by
    rw [← Finset.sum_filter,hfilter]
  rw [hsum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (Nat.mem_primesLE.mp hp).2
  let : NeZero p := ⟨hprime.ne_zero⟩
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
  by_cases hmem : p∈P
  · rw [ite_eq_left hmem]
    have hh := mul_le_mul_of_nonneg_left (hsplit p hmem) hlog
    convert hh using 1
    ring
  · rw [ite_eq_right hmem,mul_zero,add_zero]
    have h1 := rootCollisionProbability_ge_inv U hU p
    have h2 := rootCollisionProbability_ge_inv V hV p
    have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hlog
    convert hh using 1
    ring

end Ostmann.QuadraticCenter

end

end OAI
