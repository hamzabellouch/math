import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionTopology
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralLatticePowerIndex

namespace OAI

/-! # Restriction of a factor system to a quotient homomorphism -/

noncomputable section
namespace PolycyclicRecognition
variable {N Q H : Type} [Group N] [Group Q] [Group H]
  (R : NonabelianFactorSystem N Q) (f : H →* Q)

def NonabelianFactorSystem.pullback : NonabelianFactorSystem N H where
  action h := R.action (f h)
  factor h k := R.factor (f h) (f k)
  action_one := by rw [map_one, R.action_one]
  factor_one_left h := by rw [map_one, R.factor_one_left]
  factor_one_right h := by rw [map_one, R.factor_one_right]
  action_mul h k := by rw [map_mul]; exact R.action_mul _ _
  cocycle h k l := by simp only [map_mul]; exact R.cocycle _ _ _

def factorPullbackMap : FactorExtension (R.pullback f) →* FactorExtension R where
  toFun x := ⟨x.left, f x.right⟩
  map_one' := by apply FactorExtension.ext; rfl; exact map_one f
  map_mul' x y := by apply FactorExtension.ext; rfl; exact map_mul f _ _

theorem factorPullbackMap_injective (hf : Function.Injective f) :
    Function.Injective (factorPullbackMap R f) := by
  intro x y h
  apply FactorExtension.ext
  · exact congrArg (fun z : FactorExtension R => z.left) h
  · exact hf (congrArg (fun z : FactorExtension R => z.right) h)

theorem factorPullbackMap_range : (factorPullbackMap R f).range =
    f.range.comap (FactorExtension.projection R) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.right, rfl⟩
  · rintro ⟨h, hh⟩
    exact ⟨⟨x.left, h⟩, FactorExtension.ext rfl hh⟩

attribute [local instance] factorExtensionTopology
variable [TopologicalSpace N] [TopologicalSpace Q] [TopologicalSpace H]

theorem factorPullbackMap_isEmbedding (hf : Topology.IsEmbedding f) :
    Topology.IsEmbedding (factorPullbackMap R f) :=
  (factorExtensionHomeomorph R).symm.isEmbedding.comp
    ((Topology.IsEmbedding.id.prodMap hf).comp (factorExtensionHomeomorph (R.pullback f)).isEmbedding)

theorem factorPullbackMap_isClosedEmbedding (hf : Topology.IsClosedEmbedding f) :
    Topology.IsClosedEmbedding (factorPullbackMap R f) := by
  refine ⟨factorPullbackMap_isEmbedding R f hf.isEmbedding, ?_⟩
  change IsClosed ((factorPullbackMap R f).range : Set (FactorExtension R))
  rw [factorPullbackMap_range]
  exact hf.isClosed_range.preimage (continuous_factor_right R)

theorem factorPowerMap_isClosedEmbedding {n m : ℕ}
    (R : NonabelianFactorSystem N (IntegralLatticeGroup n)) (hm : 0 < m) :
    Topology.IsClosedEmbedding (factorPullbackMap R (latticePowerHom n m)) := by
  let e := MonoidHom.ofInjective (latticePowerHom_injective n hm)
  let h : IntegralLatticeGroup n ≃ₜ (latticePowerHom n m).range :=
    { e.toEquiv with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  apply factorPullbackMap_isClosedEmbedding
  exact ⟨Topology.IsEmbedding.subtypeVal.comp h.isEmbedding, isClosed_discrete _⟩

omit [TopologicalSpace N] in
theorem factorPowerMap_finiteIndex {n m : ℕ}
    (R : NonabelianFactorSystem N (IntegralLatticeGroup n)) (hm : 0 < m) :
    (factorPullbackMap R (latticePowerHom n m)).range.FiniteIndex := by
  let := latticePowerHom_finiteIndex n hm
  rw [factorPullbackMap_range]
  infer_instance

end PolycyclicRecognition

end

end OAI
