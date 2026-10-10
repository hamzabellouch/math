import Mathlib

namespace OAI

noncomputable section

noncomputable section

open scoped CStarAlgebra

namespace Kadison.CbFactor

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma similarity_of_metric (π : A →ₐ[ℂ] B) (Q : B) (hQ : IsStrictlyPositive Q)
    (hcov : ∀ a : A,π a*Q=Q*star (π (star a))) :
    ∃ S : Bˣ,∀ a : A,
      (S : B)*π (star a)*(↑(S⁻¹) : B)=star ((S : B)*π a*(↑(S⁻¹) : B)) := by
  let u : Bˣ := hQ.sqrt.isUnit.unit
  have hu : (u : B)=CFC.sqrt Q := hQ.sqrt.isUnit.unit_spec
  have hsa : IsSelfAdjoint (u : B) := hu ▸ hQ.sqrt.isSelfAdjoint
  have hsaInv : IsSelfAdjoint (↑(u⁻¹) : B) := by
    simpa only [Ring.inverse_unit] using hsa.ringInverse
  have hsq : (u : B)*(u : B)=Q := by rw [hu,CFC.sqrt_mul_sqrt_self Q hQ.nonneg]
  refine ⟨u⁻¹,?_⟩
  intro a
  simp only [inv_inv,star_mul,hsa.star_eq,hsaInv.star_eq]
  apply (u.mul_right_inj).mp
  apply (u.mul_left_inj).mp
  have h := hcov (star a)
  simp only [star_star,←hsq] at h
  simpa only [mul_assoc,Units.mul_inv_cancel_left,Units.inv_mul_cancel_right,
    Units.inv_mul,Units.mul_inv,one_mul,mul_one] using h

end Kadison.CbFactor
end
end

end OAI
