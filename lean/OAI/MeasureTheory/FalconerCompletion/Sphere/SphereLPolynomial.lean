import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.CasimirOperatorPowBound
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereShift

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set Metric MeasureTheory
open scoped ContDiff
variable {n : ℕ}

noncomputable def sphereLPolynomialND (n j : ℕ) : Polynomial ℂ :=
  stationaryLPolynomialND (sphereLeadingND n) (sphereShiftND n) j

noncomputable def sphereBPolynomialND (n j : ℕ) : Polynomial ℂ :=
  stationaryInversePolynomialND (sphereLPolynomialND n) (sphereLeadingND n)
    (sphereLeadingND_ne_zero n) j

noncomputable def sphereBND (j : ℕ) (b : SmoothFunctionND (SphereAmbientND n)) :
    SmoothFunctionND (SphereAmbientND n) :=
  differentialPolynomialND (sphereBasisND n) (sphereBPolynomialND n j) b

lemma sphereLPolynomialND_zero (n : ℕ) :
    sphereLPolynomialND n 0 = Polynomial.C (sphereLeadingND n) := stationaryLPolynomialND_zero ..

lemma sphereBPolynomialND_degree (n j : ℕ) : (sphereBPolynomialND n j).natDegree ≤ j :=
  stationaryInversePolynomialND_degree _ _ _ (sphereLPolynomialND_zero n)
    (stationaryLPolynomialND_degree _ _) j

lemma sphereLND_eq_polynomial (j : ℕ) (b : SmoothFunctionND (SphereAmbientND n)) :
    sphereLND n j b.1 = (differentialPolynomialND (sphereBasisND n) (sphereLPolynomialND n j) b).1 := by
  rw [sphereLPolynomialND,differentialPolynomialND_L]
  funext w
  simp only [sphereLND,sphereJetPolynomialND_eq]

lemma sphereBND_zero (b : SmoothFunctionND (SphereAmbientND n)) :
    (sphereBND 0 b).1 = fun w => (sphereLeadingND n)⁻¹ * b.1 w := by
  simp only [sphereBND,sphereBPolynomialND,stationaryInversePolynomialND_zero,differentialPolynomialND_C]
  rfl

lemma sphereBND_support (j : ℕ) (b : SmoothFunctionND (SphereAmbientND n)) :
    tsupport (sphereBND j b).1 ⊆ tsupport b.1 := differentialPolynomialND_support ..

noncomputable def NorthAmplitudeND.inverse (b : NorthAmplitudeND n) (j : ℕ) : NorthAmplitudeND n where
  toFun := (sphereBND j ⟨b.toFun,b.smooth⟩).1
  smooth := (sphereBND j ⟨b.toFun,b.smooth⟩).2
  support := (sphereBND_support j ⟨b.toFun,b.smooth⟩).trans b.support

lemma sphereBND_bound (j m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND (SphereAmbientND n)) (A : ℝ), 1 ≤ A →
      (∀ k ≤ m+2*j, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b.1 w‖ ≤ C*A^k) →
      ∀ k ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k (sphereBND j b).1 w‖ ≤ D*A^(k+2*j) := by
  obtain ⟨D,hD,hDb⟩ := differentialPolynomialND_bound (sphereBasisND n) (sphereBPolynomialND n j)
    j (sphereBPolynomialND_degree n j) m C hC
  refine ⟨D,hD,?_⟩
  intro b A hA hb
  simpa only [sphereBND,Nat.add_zero,Nat.zero_add] using hDb b A 0 hA (by simpa only [Nat.add_zero] using hb)

lemma sphere_inverse_cancellationND (k : ℕ) (b : SmoothFunctionND (SphereAmbientND n))
    (w : SphereAmbientND n) :
    (∑ h ∈ Finset.range (k+1), sphereLND n h (sphereBND (k-h) b).1 w) =
      if k=0 then b.1 w else 0 := by
  have he := differentialPolynomialND_inverse_convolution (sphereBasisND n) (sphereLPolynomialND n)
    (sphereLeadingND n) (sphereLeadingND_ne_zero n) (sphereLPolynomialND_zero n) k b
  have hh := congrArg (fun f : SmoothFunctionND (SphereAmbientND n) => f.1 w) he
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hh
  by_cases hk : k=0 <;>
    simpa [Submodule.coe_sum,Finset.sum_apply,sphereLND_eq_polynomial,sphereBND,
      sphereBPolynomialND,hk,Nat.succ_eq_add_one] using hh

lemma sphere_inverse_cancellation_reverseND (k : ℕ) (b : SmoothFunctionND (SphereAmbientND n))
    (w : SphereAmbientND n) :
    (∑ j ∈ Finset.range (k+1), sphereLND n (k-j) (sphereBND j b).1 w) =
      if k=0 then b.1 w else 0 := by
  rw [← sphere_inverse_cancellationND k b w,
    ← Finset.sum_range_reflect (fun h => sphereLND n h (sphereBND (k-h) b).1 w) (k+1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ k := by have := Finset.mem_range.mp hj; omega
  simp [Nat.sub_sub_self hj']

lemma sphere_inverse_triangleND (N : ℕ) (z : ℂ) (b : SmoothFunctionND (SphereAmbientND n))
    (w : SphereAmbientND n) :
    (∑ j ∈ Finset.range (N+1), ∑ h ∈ Finset.range (N+1-j),
      z^(j+h) * sphereLND n h (sphereBND j b).1 w) = b.1 w := by
  rw [← Finset.sum_range_diag_flip]
  have he : ∀ k ∈ Finset.range (N+1),
      (∑ j ∈ Finset.range (k+1), z^(j+(k-j))*sphereLND n (k-j) (sphereBND j b).1 w) =
        z^k*(if k=0 then b.1 w else 0) := by
    intro k _
    rw [← sphere_inverse_cancellation_reverseND k b w,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ k := by have := Finset.mem_range.mp hj; omega
    rw [Nat.add_sub_of_le hj']
  rw [Finset.sum_congr rfl he]
  simp

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
