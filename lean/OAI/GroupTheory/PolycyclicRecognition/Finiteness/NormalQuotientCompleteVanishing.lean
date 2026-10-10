import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalInductionTensor
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CountableFreeRetract
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FinsuppCompleteVanishing
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExactTensorCoefficient

namespace OAI

/-! # Finite-dimensional quotients propagate induced-kernel vanishing

The quotient resolution is inflated and tensored with the coefficient.
Its countable free terms are actual sums of the induced kernel coefficient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep.{0} ℤ G)

abbrev quotientTensorFunctor : Rep.{0} ℤ (G ⧸ N) ⥤ Rep.{0} ℤ G :=
  Rep.resFunctor (k := ℤ) (QuotientGroup.mk' N) ⋙ tensorLeft A

theorem quotientTensorFunctor_map_exact [Module.Flat ℤ A]
    (S : ShortComplex (Rep.{0} ℤ (G ⧸ N))) (hS : S.Exact) :
    (S.map (quotientTensorFunctor N A)).Exact :=
  representation_tensorLeft_map_exact A
    (S.map (Rep.resFunctor (k := ℤ) (QuotientGroup.mk' N)))
    (hS.map (Rep.resFunctor (k := ℤ) (QuotientGroup.mk' N)))

instance quotientTensorFunctor_preservesHomology [Module.Flat ℤ A] :
    (quotientTensorFunctor N A).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (quotientTensorFunctor_map_exact N A)

instance quotientTensorFunctor_preservesMonomorphisms [Module.Flat ℤ A] :
    (quotientTensorFunctor N A).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_map_exact _ (quotientTensorFunctor_map_exact N A)

instance quotientTensorFunctor_preservesEpimorphisms [Module.Flat ℤ A] :
    (quotientTensorFunctor N A).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_map_exact _ (quotientTensorFunctor_map_exact N A)

def quotientTensorRegularIso :
    (quotientTensorFunctor N A).obj (Rep.leftRegular ℤ (G ⧸ N)) ≅
      Rep.ind N.subtype (Rep.res N.subtype A) :=
  (β_ A (Rep.res (QuotientGroup.mk' N) (Rep.leftRegular ℤ (G ⧸ N)))) ≪≫
    (normalInductionTensorIso N A).symm

def quotientTensorFreeNatIso :
    (quotientTensorFunctor N A).obj (Rep.free ℤ (G ⧸ N) ℕ) ≅
      ((quotientTensorFunctor N A).obj (Rep.leftRegular ℤ (G ⧸ N))).finsupp ℕ :=
  Rep.finsuppTensorRight (k := ℤ) (G := G) A
    (Rep.res (QuotientGroup.mk' N) (Rep.leftRegular ℤ (G ⧸ N))) ℕ

theorem TypeFPInfinity.normalQuotient_complete_vanishing [Countable G]
    [Module.Flat ℤ A] (hG : TypeFPInfinity G)
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ p : ℕ, Subsingleton (ShiftedCompletedCohomology p
      (Rep.ind N.subtype (Rep.res N.subtype A)))) (p : ℕ) :
    Subsingleton (ShiftedCompletedCohomology p A) := by
  let : Countable (G ⧸ N) := Function.Surjective.countable (QuotientGroup.mk'_surjective N)
  have hreg (r : ℕ) : Subsingleton (ShiftedCompletedCohomology r
      ((quotientTensorFunctor N A).obj (Rep.leftRegular ℤ (G ⧸ N)))) := by
    let e := (shiftedCompletedCohomologyFunctor r).mapIso (quotientTensorRegularIso N A)
    apply subsingleton_of_forall_eq 0
    intro x
    apply e.toLinearEquiv.injective
    exact (hN r).elim _ _
  have hfree (r : ℕ) : Subsingleton (ShiftedCompletedCohomology r
      ((quotientTensorFunctor N A).obj (Rep.free ℤ (G ⧸ N) ℕ))) := by
    have hs := hG.finsupp_completeCohomology _ r (hreg r)
    let e := (shiftedCompletedCohomologyFunctor r).mapIso (quotientTensorFreeNatIso N A)
    apply subsingleton_of_forall_eq 0
    intro x
    apply e.toLinearEquiv.injective
    exact hs.elim _ _
  obtain ⟨d, hd⟩ := hQ
  have hz := exactFunctor_complete_vanishing_of_countable_free
    (quotientTensorFunctor N A) hfree (trivialIntegral (G ⧸ N)) d hd p
  let e : (quotientTensorFunctor N A).obj (trivialIntegral (G ⧸ N)) ≅ A := ρ_ A
  let ce := (shiftedCompletedCohomologyFunctor p).mapIso e
  apply subsingleton_of_forall_eq 0
  intro x
  apply ce.symm.toLinearEquiv.injective
  exact hz.elim _ _

end PolycyclicRecognition

end

end OAI
