import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicCanonicalAllowedStatement
import OAI.NumberTheory.PrimePackets.AdelicFullStatement

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set MeasureTheory
namespace PrimeDegreePackets.Adelic
 

def EveryLocalTypeAdelicRealization (d : ℕ) (hprime : (d+1).Prime) (hdegree : 5 ≤ d+1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) (hodd : Odd (d+1)) (b : Basis (Fin (d+1)) ℚ K) : Prop :=
  ∀ (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
    ∃ g : GL (Fin (d+1)) RationalFiniteAdeles, ∃ p : C(TorusQuotient K, X (d+1)),
      (matrixFullLattice hn b g).carrier = M.carrier ∧
      AllowedRealDiagonalizer b (ProjGenLinGroup.mk (realBasisGL hn b σ)) ∧
      (∀ t : (TensorAdeles K)ˣ, ambientEquiv hodd hn b (p (QuotientGroup.mk t)) =
        generalAdelicOrbit b (ProjGenLinGroup.mk (realBasisGL hn b σ)) g t) ∧
      Set.range p = packetSupport M σ ∧
      Measure.map p (adelicTorusHaar d hprime hdegree K hn) = packetMeasure M σ

 

def AdelicPacketTheorem (d : ℕ) (hprime : (d+1).Prime) (hdegree : 5 ≤ d+1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) (hodd : Odd (d+1))
    (b : Basis (Fin (d+1)) ℚ K) (h : PGL(Fin (d+1), ℝ))
    (g : GL (Fin (d+1)) RationalFiniteAdeles) : Prop :=
  AdelicPacketProposition d hprime hdegree K hn hodd b h g ∧
  EveryLocalTypeAdelicRealization d hprime hdegree K hn hodd b ∧
  ∀ σ : OrderedEmbeddings (d+1) K, CanonicalRealDiagonalizerAllowed hn b σ
end PrimeDegreePackets.Adelic

end

end OAI
