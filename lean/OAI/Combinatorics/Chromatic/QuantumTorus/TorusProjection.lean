import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PowerSeriesThreeFactors
import OAI.Combinatorics.Chromatic.GradedAlgebra.HNSeries
import OAI.Combinatorics.Chromatic.GradedAlgebra.ProjectionRecursion

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries ElementaryPositivity.WeightedTorusSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (h : M →+ ℝ)
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid

lemma sum_monomials (f : Torus v Ω) :
    (∑m∈f.support,Torus.monomial v Ω m (f m))=f := Finsupp.sum_single f

lemma zeroProject_monomial (m : M) (r : R) :
    zeroProject v Ω h (Torus.monomial v Ω m r)=
      if h m=0 then Torus.monomial v Ω m r else 0 := filter_monomial v Ω _ m r

lemma zeroProject_monomial_mul (a b : M) (x y : R) (ha : h a≤0) (hb : h b≤0) :
    zeroProject v Ω h (Torus.monomial v Ω a x*Torus.monomial v Ω b y)=
      zeroProject v Ω h (Torus.monomial v Ω a x)*
      zeroProject v Ω h (Torus.monomial v Ω b y) := by
  classical
  rw [Torus.monomial_mul_monomial]
  simp only [zeroProject_monomial,map_add]
  by_cases ha0 : h a=0
  · by_cases hb0 : h b=0
    · simp only [ha0,hb0,add_zero,ite_true,Torus.monomial_mul_monomial]
    · have hab : h a+h b≠0 := by simpa only [ha0,zero_add] using hb0
      simp only [ha0,zero_add,hb0,ite_true,ite_false,Torus.mul_zero]
  · have hab : h a+h b≠0 := by intro H; exact ha0 (by linarith)
    simp only [ha0,hab,ite_false,Torus.zero_mul]

lemma zeroProject_mul_nonpositive (f g : Torus v Ω)
    (hf : f∈supportedSubring v Ω (nonpositiveCone h))
    (hg : g∈supportedSubring v Ω (nonpositiveCone h)) :
    zeroProject v Ω h (f*g)=zeroProject v Ω h f*zeroProject v Ω h g := by
  classical
  have H : zeroProject v Ω h ((∑m∈f.support,Torus.monomial v Ω m (f m))*
      (∑n∈g.support,Torus.monomial v Ω n (g n)))=
      zeroProject v Ω h (∑m∈f.support,Torus.monomial v Ω m (f m))*
      zeroProject v Ω h (∑n∈g.support,Torus.monomial v Ω n (g n)) := by
    simp only [torus_sum_mul,torus_mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    apply zeroProject_monomial_mul
    · by_contra H
      exact (Finsupp.mem_support_iff.mp hn) (hf n H)
    · by_contra H
      exact (Finsupp.mem_support_iff.mp hm) (hg m H)
  simpa only [sum_monomials] using H

lemma zeroProject_one : zeroProject v Ω h (1 : Torus v Ω)=1 := by
  classical
  change (Finsupp.filterAddHom (fun m=>h m=0) : Torus v Ω →+ Torus v Ω)
    (Torus.monomial v Ω 0 1)=Torus.monomial v Ω 0 1
  rw [filter_monomial,map_zero,ite_eq_left rfl]

lemma zeroFactor_coeff_projection (f : PowerSeries (Torus v Ω)) (n : ℕ) :
    coeff n (PowerSeriesSplit.zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) f)=
      zeroProject v Ω h (coeff n (PowerSeriesSplit.rightFactor (positiveProject v Ω h) f)) := by
  apply PowerSeriesSplit.left_coeff_projection (zeroProject v Ω h)
    (supportedSubring v Ω (nonpositiveCone h)) (zeroProject_idem v Ω h) (zeroProject_one v Ω h)
  · intro x hx
    exact (nonpositive_iff v Ω h _).mpr (positive_zero_project v Ω h x)
  · intro x hx y hy
    exact zeroProject_mul_nonpositive v Ω h x y hx hy
  · exact PowerSeriesSplit.right_constant _ _
  · intro k
    cases k with
    | zero => rw [coeff_zero_eq_constantCoeff_apply,PowerSeriesSplit.right_constant]; exact Subring.one_mem _
    | succ k =>
      exact (nonpositive_iff v Ω h _).mpr
        (PowerSeriesSplit.right_killed _ (positiveProject_idem v Ω h) f k)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
