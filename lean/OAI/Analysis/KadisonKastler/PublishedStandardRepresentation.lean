import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism
import OAI.Analysis.KadisonKastler.SpatialProduct

namespace OAI

/-! # Faithful cyclic representations and tensor functoriality

Blackadar, *Operator Algebras*, III.2.2.29 (p.273), supplies a faithful
normal state for a countably decomposable algebra. Its normal GNS
representation (III.2.2.1--3, pp.265--266) is faithful, with a cyclic
separating unit vector; on a separably acting algebra it is separable
(III.2.1.4 and III.2.2.8). This does not claim that the original
representation has a cyclic separating vector.

The tensor extension of a normal star isomorphism is the isomorphism
case of III.2.2.5 (p.267). Algebraic star isomorphisms between von
Neumann algebras are automatically normal (III.2.2.1, III.2.2.12).
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

structure FaithfulCyclicRepresentation {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) where
  K : Type u
  [normedK : NormedAddCommGroup K]
  [innerK : InnerProductSpace ℂ K]
  [completeK : CompleteSpace K]
  [nontrivialK : Nontrivial K]
  [separableK : TopologicalSpace.SeparableSpace K]
  algebra : VonNeumannAlgebra K
  equiv : Algebra M ≃⋆ₐ[ℂ] Algebra algebra
  vector : K
  unit_vector : ‖vector‖ = 1
  cyclic : DenseRange (algebraVectorMap algebra vector)
  separating : Function.Injective (algebraVectorMap algebra vector)

attribute [instance] FaithfulCyclicRepresentation.normedK FaithfulCyclicRepresentation.innerK
  FaithfulCyclicRepresentation.completeK FaithfulCyclicRepresentation.nontrivialK
  FaithfulCyclicRepresentation.separableK

def PublishedFaithfulCyclicRepresentation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] [TopologicalSpace.SeparableSpace H] (M : VonNeumannAlgebra H),
    Nonempty (FaithfulCyclicRepresentation M)

def PublishedSpatialTensorStarIsomorphism : Prop :=
  ∀ (H K L : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (D : VonNeumannAlgebra L),
    (Algebra M ≃⋆ₐ[ℂ] Algebra N) →
    Nonempty (Algebra (spatialProductAlgebra M D) ≃⋆ₐ[ℂ]
      Algebra (spatialProductAlgebra N D))

end

end KadisonKastler

end OAI
