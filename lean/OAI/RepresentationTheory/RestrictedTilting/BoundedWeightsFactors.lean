import OAI.RepresentationTheory.RestrictedTilting.BoundedOriginTarget

namespace OAI

namespace FiberFunctorProof
universe u
variable (k : Type u) [Field k] [Infinite k]

 

lemma allSimpleFactorsHighestBelow_of_weights {M : Type u} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) (hρ : IsRational k ρ) (d q : ℕ) (hdq : d < q)
    (hb : HasWeightsBetween ρ (-(d : ℤ)) d) : AllSimpleFactorsHighestBelow ρ q := by
  intro A B _ i π hi hπ he
  let : Nontrivial (Representation.asModule B.ρ) :=
    IsSimpleModule.nontrivial (MonoidAlgebra k (SL2 k)) (Representation.asModule B.ρ)
  let : Nontrivial B := (Representation.asModuleEquiv B.ρ).symm.toEquiv.nontrivial
  have hA := IsRational.of_injective k A.ρ ρ i hi he hρ
  have hB := IsRational.of_surjective k A.ρ B.ρ (fdrepLinear k π) hπ (fdrepLinear_comm k π) hA
  have hbA := hasWeightsBetween_of_injective k A.ρ ρ i hi he _ _ hb
  have hbB := hasWeightsBetween_of_surjective k A.ρ B.ρ hA (fdrepLinear k π) hπ
    (fdrepLinear_comm k π) _ _ hbA
  obtain ⟨n,hn,hwn,v,hv,hwv⟩ := exists_highest_in_bound k B.ρ hB d hbB
  refine ⟨n,hn.trans_lt hdq,hwn,v,hv,hwv,?_⟩
  exact highest_unipotent_fixed B.ρ hB n v hwv (fun m w hm => hwn m w (Or.inr hm))
end FiberFunctorProof

end OAI
