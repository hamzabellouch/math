import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import OAI.Analysis.Laughlin.Spin.PolynomialDegree

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

noncomputable def particleDegreeWeight {N : ℕ} (k : Fin N) (ib : SpinorVariables N) : ℕ :=
  if ib.1=k then 1 else 0

theorem particleDegreeWeight_apply {N : ℕ} (k : Fin N) (d : SpinorVariables N →₀ ℕ) :
    Finsupp.weight (particleDegreeWeight k) d=d (k,false)+d (k,true) := by
  rw [Finsupp.weight_eq_sum,Fintype.sum_prod_type]
  simp [particleDegreeWeight,Nat.add_comm]

theorem monomialExponent_particle_degree {N Q : ℕ} (a : Configuration N Q) (k : Fin N) :
    Finsupp.weight (particleDegreeWeight k) (monomialExponent a)=Q := by
  rw [particleDegreeWeight_apply]
  simp only [monomialExponent,Finsupp.onFinset_apply,Bool.false_eq_true,↓reduceIte]
  omega

theorem spinPolynomial_particle_degree {N Q : ℕ} (ψ : State N Q) (k : Fin N) :
    (spinPolynomial ψ).IsWeightedHomogeneous (particleDegreeWeight k) Q := by
  apply IsWeightedHomogeneous.sum
  intro a ha
  exact isWeightedHomogeneous_monomial _ _ _ (monomialExponent_particle_degree a k)

theorem exponent_eq_configuration {N Q : ℕ} (d : SpinorVariables N →₀ ℕ)
    (hd : ∀ k : Fin N, d (k,false)+d (k,true)=Q) :
    ∃ a : Configuration N Q, monomialExponent a=d := by
  let a : Configuration N Q := fun k => ⟨d (k,true),by have h := hd k; omega⟩
  refine ⟨a,?_⟩
  ext ⟨k,b⟩
  cases b <;> simp only [monomialExponent,Finsupp.onFinset_apply,Bool.false_eq_true,↓reduceIte,a]
  have h := hd k
  omega

theorem spinPolynomial_reconstruct {N Q : ℕ} (P : MvPolynomial (SpinorVariables N) ℂ)
    (hP : ∀ k : Fin N, P.IsWeightedHomogeneous (particleDegreeWeight k) Q) :
    spinPolynomial (fun a : Configuration N Q => P.coeff (monomialExponent a)/spinWeight a)=P := by
  ext d
  by_cases hd : P.coeff d=0
  · by_cases he : ∃ a : Configuration N Q, monomialExponent a=d
    · obtain ⟨a,rfl⟩ := he
      rw [spinPolynomial_coeff]
      simp [hd]
    · rw [hd]
      simp only [spinPolynomial,coeff_sum,coeff_monomial]
      apply Finset.sum_eq_zero
      intro a ha
      simp only [ite_eq_right (fun h => he ⟨a,h⟩)]
  · obtain ⟨a,rfl⟩ := exponent_eq_configuration d (fun k => by
      rw [← particleDegreeWeight_apply]; exact hP k hd)
    rw [spinPolynomial_coeff]
    field_simp [spinWeight_ne_zero a]

end Laughlin

end OAI
