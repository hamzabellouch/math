import Mathlib
import OAI.Analysis.Commutator.NormalGNS
import OAI.Analysis.Commutator.TracialRightClosure

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace Topology ComplexOrder

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma rightMul_eq_left_of_commutative (hc : ∀ a b : M,a*b=b*a)
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (a : M) :
    rightMul τ hτ a=τ.gnsStarAlgHom a := by
  ext x
  refine (algebraVector_dense τ).induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [algebraVector_apply,rightMul_coe,PositiveLinearMap.ofPreGNS_toPreGNS,left_coe,hc b a]

theorem commutant_range_eq_of_commutative (hc : ∀ a b : M,a*b=b*a)
    (hn : BoundedWOTContinuous M τ) :
    Set.centralizer (Set.range τ.gnsStarAlgHom)=Set.range τ.gnsStarAlgHom := by
  have ht : ∀ a b : M,τ (a*b)=τ (b*a) := fun a b => congrArg τ (hc a b)
  apply Set.Subset.antisymm
  · intro T hT
    obtain ⟨b,hb,hTb,_⟩ := TracialGNS.commutation τ ht hT
    rw [range_bicommutant M τ ht hn] at hb
    obtain ⟨a,rfl⟩ := hb
    refine ⟨a,?_⟩
    rw [rightOperator_original] at hTb
    exact (hTb.trans (rightMul_eq_left_of_commutative M τ hc ht a)).symm
  · rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    exact (map_mul τ.gnsStarAlgHom b a).symm.trans
      ((congrArg τ.gnsStarAlgHom (hc b a)).trans (map_mul τ.gnsStarAlgHom a b))

end Kadison.NormalGNS

end

end
end

end OAI
