import OAI.AlgebraicGeometry.AbhyankarSathaye.LiftingIdentities
import Mathlib.RingTheory.Polynomial.Quotient

namespace OAI

/-!
# Elimination of compatible linear equations

A Bézout relation identifies the ideal of two compatible linear equations
with a single evaluation relation, over any commutative ring.
-/

noncomputable section
namespace AbhyankarSathaye

theorem linear_ideal {B : Type*} [CommRing B] (h c a b r q W : B)
    (hc : c*a = h*b) (hb : r*h+q*c = 1) :
    Ideal.span ({h*W-a, c*W-b} : Set B) = Ideal.span {W-(r*a+q*b)} := by
  have hh := solve_h h c a b r q hc hb
  have hy := solve_c h c a b r q hc hb
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have he : h*W-a = h*(W-(r*a+q*b)) := by rw [mul_sub, hh]
      rw [he]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · have he : c*W-b = c*(W-(r*a+q*b)) := by rw [mul_sub, hy]
      rw [he]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    have he : W-(r*a+q*b) = r*(h*W-a)+q*(c*W-b) := by
      calc
        _ = (r*h+q*c)*W-(r*a+q*b) := by rw [hb, one_mul]
        _ = _ := by ring
    rw [he]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

def linear_equations_quotient_equiv {B : Type*} [CommRing B]
    (h c a b r q : B) (hc : c*a = h*b) (hb : r*h+q*c = 1) :
    (Polynomial B ⧸ Ideal.span
      {Polynomial.C h*Polynomial.X-Polynomial.C a,
       Polynomial.C c*Polynomial.X-Polynomial.C b}) ≃ₐ[B] B := by
  have hc' : Polynomial.C c*Polynomial.C a = Polynomial.C h*Polynomial.C b := by
    simpa using congrArg (Polynomial.C : B →+* Polynomial B) hc
  have hb' : Polynomial.C r*Polynomial.C h+Polynomial.C q*Polynomial.C c = 1 := by
    simpa using congrArg (Polynomial.C : B →+* Polynomial B) hb
  have hi := linear_ideal (Polynomial.C h) (Polynomial.C c) (Polynomial.C a)
    (Polynomial.C b) (Polynomial.C r) (Polynomial.C q) Polynomial.X hc' hb'
  simp only [← map_mul, ← map_add] at hi
  exact (Ideal.quotientEquivAlgOfEq B hi).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (r*a+q*b))

end AbhyankarSathaye

end

end OAI
