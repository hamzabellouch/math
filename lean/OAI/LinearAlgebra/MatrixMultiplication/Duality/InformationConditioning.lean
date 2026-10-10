import OAI.LinearAlgebra.MatrixMultiplication.Completion.Conditioning
import OAI.LinearAlgebra.MatrixMultiplication.Duality.Information

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualInformation

open MatrixMultiplication.Foundation CompletionLaws
attribute [local instance] Classical.propDecidable Classical.decEq

variable {A R L X : Type*} [Fintype A] [Fintype R] [Fintype L] [Fintype X]

theorem conditionalMassFactorization_condition (p : FiniteLaw A)
    (prior : A → R) (label : A → L) (x : A → X) (Q : R → Prop)
    (h : 0 < eventMass p (fun a => Q (prior a)))
    (factor : ConditionalMassFactorization p prior label x) :
    ConditionalMassFactorization (condition p (fun a => Q (prior a)) h)
      (fun a => prior a.val) (fun a => label a.val) (fun a => x a.val) := by
  intro r l xx
  have hj := condition_coordinate_mass p (fun a => (prior a, (label a, x a)))
    (fun v => Q v.1) h (r, (l, xx))
  have hr := condition_coordinate_mass p prior Q h r
  have hl := condition_coordinate_mass p (fun a => (prior a, label a))
    (fun v => Q v.1) h (r, l)
  have hx := condition_coordinate_mass p (fun a => (prior a, x a))
    (fun v => Q v.1) h (r, xx)
  change
    ((condition p (fun a => Q (prior a)) h).map
      (fun a => (prior a.val, (label a.val, x a.val)))).mass (r, (l, xx)) *
        ((condition p (fun a => Q (prior a)) h).map (fun a => prior a.val)).mass r =
      ((condition p (fun a => Q (prior a)) h).map
        (fun a => (prior a.val, label a.val))).mass (r, l) *
          ((condition p (fun a => Q (prior a)) h).map
            (fun a => (prior a.val, x a.val))).mass (r, xx)
  rw [hj, hr, hl, hx]
  by_cases hQ : Q r
  · simp only [hQ, ite_true]
    rw [div_mul_div_comm, div_mul_div_comm, factor r l xx]
  · simp only [hQ, ite_false, zero_mul]

theorem conditionalIndependent_condition_of_mass_factorization (p : FiniteLaw A)
    (prior : A → R) (label : A → L) (x : A → X) (Q : R → Prop)
    (h : 0 < eventMass p (fun a => Q (prior a)))
    (factor : ConditionalMassFactorization p prior label x) :
    ConditionalIndependent (condition p (fun a => Q (prior a)) h)
      (fun a => prior a.val) (fun a => label a.val) (fun a => x a.val) :=
  conditionalIndependent_of_mass_factorization _ _ _ _
    (conditionalMassFactorization_condition p prior label x Q h factor)

theorem conditionalIndependent_condition (p : FiniteLaw A)
    (prior : A → R) (label : A → L) (x : A → X) (Q : R → Prop)
    (h : 0 < eventMass p (fun a => Q (prior a)))
    (independent : ConditionalIndependent p prior label x) :
    ConditionalIndependent (condition p (fun a => Q (prior a)) h)
      (fun a => prior a.val) (fun a => label a.val) (fun a => x a.val) :=
  conditionalIndependent_condition_of_mass_factorization p prior label x Q h
    (mass_factorization_of_conditionalIndependent p prior label x independent)

end MatrixMultiplication.DualInformation

end

end OAI
