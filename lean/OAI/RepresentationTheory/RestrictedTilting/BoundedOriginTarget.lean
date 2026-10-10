import OAI.RepresentationTheory.RestrictedTilting.Basic

namespace OAI

namespace FiberFunctorProof
open CategoryTheory
open scoped Pointwise
universe u
noncomputable section

 

structure EquivariantPlaneBundle (k : Type u) [Field k] where
  Sections : Type u
  [addCommGroup : AddCommGroup Sections]
  [fieldModule : Module k Sections]
  [planeModule : Module (MvPolynomial (Fin 2) k) Sections]
  [scalarTower : IsScalarTower k (MvPolynomial (Fin 2) k) Sections]
  finite : Module.Finite (MvPolynomial (Fin 2) k) Sections
  projective : Module.Projective (MvPolynomial (Fin 2) k) Sections
  action : Representation k (SL2 k) Sections
  rational : IsRational k action
  compatible : PlaneCompatible k action

attribute [instance] EquivariantPlaneBundle.addCommGroup EquivariantPlaneBundle.fieldModule
  EquivariantPlaneBundle.planeModule EquivariantPlaneBundle.scalarTower

variable {k : Type u} [Field k]

 

def planePointIdeal (a : Fin 2 → k) : Ideal (MvPolynomial (Fin 2) k) :=
  RingHom.ker (MvPolynomial.eval a)

def EquivariantPlaneBundle.fibreRelation (B : EquivariantPlaneBundle k) (a : Fin 2 → k) :
    Submodule k B.Sections :=
  ((planePointIdeal a • (⊤ : Submodule (MvPolynomial (Fin 2) k) B.Sections))).restrictScalars k

abbrev EquivariantPlaneBundle.fibre (B : EquivariantPlaneBundle k) (a : Fin 2 → k) :=
  B.Sections ⧸ B.fibreRelation a

 

def HasHighestWeight {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k (SL2 k) V) (n : ℕ) : Prop :=
  HasWeightsBetween ρ (-(n : ℤ)) n ∧ ∃ v : V, v ≠ 0 ∧
    (∀ a, ρ (diagonalTorus k a) v = integerCharacter k n a • v) ∧
    ∀ t, ρ (unipotent k t) v = v

 

def AllSimpleFactorsHighestBelow {M : Type u} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) (q : ℕ) : Prop :=
  ∀ (A B : FDRep k (SL2 k)) [Representation.IsIrreducible B.ρ]
    (i : A →ₗ[k] M) (π : A ⟶ B), Function.Injective i →
    Function.Surjective π.hom.hom.hom →
    (∀ g v, i (A.ρ g v) = ρ g (i v)) →
    ∃ n : ℕ, n < q ∧ HasHighestWeight B.ρ n

 

def BoundedOriginTheorem : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : ℕ), 1 ≤ r → ∀ (l : (Fin r → ZMod p) →+ k), Function.Injective l →
    ∀ (D : FDRep k (Multiplicative (Fin r → ZMod p))),
    ∃ B : EquivariantPlaneBundle k,
      (∃ e : B.fibre ![1,0] ≃ₗ[k] D,
        ∀ (g : Multiplicative (Fin r → ZMod p)) (v : B.Sections),
          e ((B.fibreRelation ![1,0]).mkQ (B.action (elementaryEmbedding k p r l g) v)) =
            D.ρ g (e ((B.fibreRelation ![1,0]).mkQ v))) ∧
      Module.Finite k (B.fibre 0) ∧
      ∃ σ₀ : Representation k (SL2 k) (B.fibre 0),
        (∀ g v, σ₀ g ((B.fibreRelation 0).mkQ v) =
          (B.fibreRelation 0).mkQ (B.action g v)) ∧
        IsRational k σ₀ ∧ AllSimpleFactorsHighestBelow σ₀ (p^r)

end
end FiberFunctorProof

end OAI
