import OAI.LinearAlgebra.MatrixMultiplication.Entropy.IndependentConditioning
import OAI.LinearAlgebra.MatrixMultiplication.Duality.Information

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualInformation

open MatrixMultiplication.Foundation CompletionLaws
attribute [local instance] Classical.propDecidable Classical.decEq

variable {A L X : Type*} [Fintype A] [Fintype L] [Fintype X]

theorem mass_factorization_const_iff (p : FiniteLaw A)
    (label : A → L) (x : A → X) :
    ConditionalMassFactorization p (fun _ => PUnit.unit) label x ↔
      ∀ l xx, (p.map (fun a => (label a, x a))).mass (l, xx) =
        (p.map label).mass l * (p.map x).mass xx := by
  classical
  constructor
  · intro h l xx
    have hf := h PUnit.unit l xx
    simpa [FiniteLaw.map_mass, Prod.mk.injEq, p.total] using hf
  · intro h r l xx
    cases r
    simpa [FiniteLaw.map_mass, Prod.mk.injEq, p.total] using h l xx

theorem conditionalMassFactorization_condition_label (p : FiniteLaw A)
    (label : A → L) (x : A → X) (Q : L → Prop)
    (h : 0 < eventMass p (fun a => Q (label a)))
    (factor : ConditionalMassFactorization p (fun _ => PUnit.unit) label x) :
    ConditionalMassFactorization (condition p (fun a => Q (label a)) h)
      (fun _ => PUnit.unit) (fun a => label a.val) (fun a => x a.val) := by
  have independent := (mass_factorization_const_iff p label x).mp factor
  have swapped : ∀ xx l,
      (p.map (fun a => (x a, label a))).mass (xx, l) =
        (p.map x).mass xx * (p.map label).mass l := by
    intro xx l
    have hm : (p.map (fun a => (x a, label a))).mass (xx, l) =
        (p.map (fun a => (label a, x a))).mass (l, xx) := by
      simp only [FiniteLaw.map_mass, Prod.mk.injEq, and_comm]
    rw [hm, independent l xx, mul_comm]
  apply (mass_factorization_const_iff _ _ _).mpr
  intro l xx
  have hj := condition_coordinate_mass p (fun a => (label a, x a))
    (fun v => Q v.1) h (l, xx)
  have hl := condition_coordinate_mass p label Q h l
  have hx := condition_independent_coordinate_mass p x label Q swapped h xx
  rw [hj, hl, hx]
  by_cases hQ : Q l
  · simp only [hQ, ite_true]
    rw [independent l xx]
    ring
  · simp only [hQ, ite_false, zero_mul]

end MatrixMultiplication.DualInformation

end

end OAI
