import Mathlib
import OAI.GroupTheory.SimpleOvergroups.ActionCorner
import OAI.GroupTheory.SimpleOvergroups.RingModel
import OAI.GroupTheory.SimpleOvergroups.SourceRingReduction

namespace OAI


noncomputable section
namespace SimpleFInftyOvergroups.SourceModel
open scoped Classical
open FiniteAlgebraicEnvelopes RingAssembly

variable {G : Type} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1))

def actionCornerMap : ActionMon s h →*₀ (e_idempotent s h).Corner :=
  (cornerMap s h).toMonoidWithZeroHom.comp
    ((monoidBasis₀ (k:=ZMod 2) (M:=L s h)).comp (codeAction₀ s h))

theorem actionCornerMap_injective : Function.Injective (actionCornerMap s h) :=
  (cornerMap_injective s h).comp
    ((monoidBasis_injective (k:=ZMod 2) (M:=L s h)).comp (codeAction_injective s h))

def groupCornerMap (hs : Subgroup.closure (Set.range s)=⊤) : G →* (e_idempotent s h).Corner :=
  (cornerMap s h).toMonoidHom.comp ((ContractedPresentation.monoidBasis (ZMod 2)).comp (codeG s h hs))

theorem groupCornerMap_injective (hs : Subgroup.closure (Set.range s)=⊤) :
    Function.Injective (groupCornerMap s h hs) :=
  (cornerMap_injective s h).comp
    ((monoidBasis_injective (k:=ZMod 2) (M:=L s h)).comp (codeG_injective s h hs))

def data (hs : Subgroup.closure (Set.range s)=⊤) : SourceRingData G where
  R := B s h
  ringR := bRing s h
  nontrivialR := bNontrivial s h
  algebraR := bAlgebra s h
  φ := φ s h
  φ_injective := φ_injective s h
  binary := binary s h
  e := e s h
  e_idempotent := e_idempotent s h
  e_nonzero := e_nonzero s h
  S y := actionCornerMap s h (SourceActionMonoid.prepend y)
  T y := actionCornerMap s h (SourceActionMonoid.delete y)
  TS y z := by
    by_cases hyz : y=z
    · simpa only [ite_eq_left hyz] using corner_TS (actionCornerMap s h) y z
    · simpa only [ite_eq_right hyz] using corner_TS (actionCornerMap s h) y z
  ρ := actionUnits (actionCornerMap s h)
  ρ_injective := actionUnits_injective (actionCornerMap s h) (actionCornerMap_injective s h)
  ρS := corner_ρS (actionCornerMap s h)
  Tρ := corner_Tρ (actionCornerMap s h)
  A := Generators s h
  finiteA := inferInstance
  π := presentationMap s h
  π_surjective := presentationMap_surjective s h
  rel := differences (Relations s h)
  rel_finite := differences_finite _ (relations_finite s h)
  ker_π := presentationMap_kernel s h
  g := (groupCornerMap s h hs).toHomUnits
  g_injective := fun _ _ hxy => groupCornerMap_injective s h hs (congrArg Units.val hxy)

end SourceModel

theorem sourceRingProducer : SourceRingProducerObligation := by
  intro G _ hG
  obtain ⟨k,s,hs,hw⟩ := hG
  exact ⟨SourceModel.data s hw hs⟩

universe u

theorem main (G : Type u) [Group G] [Group.FG G] (hG : HasDecidableWordProblem G) :
    ∃ (H : Type u) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      HasTypeFInfty H ∧ ∃ f : G →* H, Function.Injective f :=
  main_of_sourceRingProducer sourceRingProducer G hG

end SimpleFInftyOvergroups
end

end OAI
