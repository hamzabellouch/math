import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicGeneralPacketDefinitions

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set MeasureTheory
namespace PrimeDegreePackets.Adelic

 

def AdelicPacketProposition (d : ℕ) (hprime : (d+1).Prime) (hdegree : 5 ≤ d+1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) (hodd : Odd (d+1))
    (b : Basis (Fin (d+1)) ℚ K) (h : PGL(Fin (d+1), ℝ))
    (g : GL (Fin (d+1)) RationalFiniteAdeles) : Prop :=
  CompactSpace (TorusQuotient K) ∧
  (((matrixFullLattice hn b g).carrier : Set K) = finiteGlobalMatrixLattice b g ∧
    ∀ p : Nat.Primes, completedLattice p.val (matrixFullLattice hn b g) = localMatrixLattice b g p) ∧
  (IsProbabilityMeasure (adelicTorusHaar d hprime hdegree K hn) ∧
    Measure.IsHaarMeasure (adelicTorusHaar d hprime hdegree K hn)) ∧
  (∃ σ : OrderedEmbeddings (d+1) K, ∃ p : C(TorusQuotient K, X (d+1)),
    (∀ t : (TensorAdeles K)ˣ, ambientEquiv hodd hn b (p (QuotientGroup.mk t)) =
      generalAdelicOrbit b h g t) ∧
    Set.range p = packetSupport (matrixFullLattice hn b g) σ ∧
    Measure.map p (adelicTorusHaar d hprime hdegree K hn) =
      packetMeasure (matrixFullLattice hn b g) σ) ∧
  (∀ M : FullLattice (d+1) K, ∃ g' : GL (Fin (d+1)) RationalFiniteAdeles,
    finiteGlobalMatrixLattice b g' = (M.carrier : Set K)) ∧
  (∀ (m : Basis (Fin (d+1)) ℚ K) (t : (TensorAdeles K)ˣ),
    generalAdelicOrbit m
      (ProjGenLinGroup.mk (GeneralLinearGroup.map (algebraMap ℚ ℝ) (rowBasisChange m b)) * h)
      (GeneralLinearGroup.map rationalFiniteEmbedding (rowBasisChange m b) * g) t =
      generalAdelicOrbit b h g t) ∧
  (∀ g' : GL (Fin (d+1)) RationalFiniteAdeles, ProjGenLinGroup.mk g = ProjGenLinGroup.mk g' →
    ∀ t : (TensorAdeles K)ˣ, generalAdelicOrbit b h g t = generalAdelicOrbit b h g' t) ∧
  (∃ σ : OrderedEmbeddings (d+1) K, ∃ z : (Fin (d+1) → ℝ)ˣ,
    h = ProjGenLinGroup.mk (realBasisGL hn b σ * diagonalUnits (d+1) z))

end PrimeDegreePackets.Adelic

end

end OAI
