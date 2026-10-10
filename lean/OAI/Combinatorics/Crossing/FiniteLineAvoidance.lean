import OAI.Combinatorics.Crossing.PlanarSegments
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators Classical

def lineAvoidancePolynomial (z a v : Plane) : ℝ[X] :=
  C v.2 * X - C v.1 * X^2 + C (det2 (z-a) v)

theorem lineAvoidancePolynomial_eval (z a v : Plane) (t : ℝ) :
    (lineAvoidancePolynomial z a v).eval t = det2 (z+(t,t^2)-a) v := by
  simp [lineAvoidancePolynomial,det2]
  ring

theorem lineAvoidancePolynomial_ne_zero (z a v : Plane) (hv : v ≠ 0) :
    lineAvoidancePolynomial z a v ≠ 0 := by
  intro h
  have h₁ := congrArg (fun p : ℝ[X] => p.coeff 1) h
  have h₂ := congrArg (fun p : ℝ[X] => p.coeff 2) h
  norm_num [lineAvoidancePolynomial,coeff_C_mul] at h₁ h₂
  apply hv
  exact Prod.ext h₂ h₁

theorem exists_near_avoiding_lines {ι : Type*} [Fintype ι] (a v : ι → Plane)
    (hv : ∀ i, v i ≠ 0) (z : Plane) (ε : ℝ) (hε : 0 < ε) :
    ∃ o : Plane, dist o z < ε ∧ ∀ i, det2 (o-a i) (v i) ≠ 0 := by
  let bad : Finset ℝ := Finset.univ.biUnion (fun i => (lineAvoidancePolynomial z (a i) (v i)).roots.toFinset)
  have hδ : 0 < min ε 1 := lt_min hε (by norm_num)
  obtain ⟨t,ht⟩ := ((Set.Ioo_infinite hδ).sdiff bad.finite_toSet).nonempty
  have ht0 : 0 < t := ht.1.1
  have htε : t < ε := lt_of_lt_of_le ht.1.2 (min_le_left _ _)
  have ht1 : t < 1 := lt_of_lt_of_le ht.1.2 (min_le_right _ _)
  refine ⟨z+(t,t^2),?_,?_⟩
  · have ht2 : t^2 < ε := by nlinarith
    simp only [Prod.dist_eq,Prod.fst_add,Prod.snd_add,Real.dist_eq,add_sub_cancel_left]
    exact max_lt (by simpa [abs_of_pos ht0] using htε) (by simpa [abs_of_nonneg (sq_nonneg t)] using ht2)
  · intro i hi
    have hp : (lineAvoidancePolynomial z (a i) (v i)).eval t = 0 := by
      rwa [lineAvoidancePolynomial_eval]
    apply ht.2
    change t ∈ bad
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ i,?_⟩
    simpa [mem_roots (lineAvoidancePolynomial_ne_zero z (a i) (v i) (hv i))] using hp

end Zarankiewicz

end

end OAI
