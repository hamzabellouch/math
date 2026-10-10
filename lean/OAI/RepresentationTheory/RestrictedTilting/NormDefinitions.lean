import Mathlib

namespace OAI

namespace FiberFunctorProof
open CategoryTheory Representation
universe u v
variable {k : Type u} [Field k] {G : Type v} [Group G] [Fintype G]
variable {V : Type u} [AddCommGroup V] [Module k V]

 
noncomputable def normToInvariants (ρ : Representation k G V) : V →ₗ[k] ρ.invariants :=
  ρ.norm.codRestrict _ (fun v g => ρ.self_norm_apply g v)

 
noncomputable def coinvariantNorm (ρ : Representation k G V) :
    Coinvariants ρ →ₗ[k] ρ.invariants :=
  Coinvariants.lift ρ (normToInvariants ρ) (fun g => by
    ext v
    exact ρ.norm_self_apply g v)

@[simp] theorem coinvariantNorm_mk (ρ : Representation k G V) (v : V) :
    (coinvariantNorm ρ (Coinvariants.mk ρ v) : V) = ρ.norm v := rfl

 

def NormProjectivityTheorem : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p],
    (∀ (H : Type u) [Group H] [Fintype H], IsPGroup p H →
      ∀ (M : Type u) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
      (ρ : Representation k H M),
      Projective (Rep.of ρ) ↔ Function.Bijective (coinvariantNorm ρ)) ∧
    (∀ (G : Type u) [Group G] [Fintype G]
      (M : Type u) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
      (ρ : Representation k G M),
      Projective (Rep.of ρ) → Function.Bijective (coinvariantNorm ρ))
end FiberFunctorProof

end OAI
