import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicFlow
import OAI.NumberTheory.PrimePackets.AdelicHaarAveraging

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise MatrixGroups
open Matrix Module Filter Set MeasureTheory
namespace PrimeDegreePackets.Adelic

lemma range_adelicTorusPoint {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hodd : Odd (d+1)) (hn : finrank ℚ K = d+1)
    (b : Basis (Fin (d+1)) ℚ K) (σ : OrderedEmbeddings (d+1) K)
    (g : GL (Fin (d+1)) RationalFiniteAdeles) :
    Set.range (adelicTorusPoint hodd hn b σ g) = packetSupport (matrixFullLattice hn b g) σ := by
  ext x
  constructor
  · rintro ⟨q,rfl⟩
    induction q using QuotientGroup.induction_on with | H t =>
    have H : ambientEquiv hodd hn b (adelicTorusPoint hodd hn b σ g (QuotientGroup.mk t)) ∈
        adelicPacketSupport hn b σ g := by
      refine ⟨t,?_⟩
      exact ((ambientEquiv hodd hn b).apply_symm_apply _).symm
    rw [← adelic_packet_support_eq hodd hn b σ g] at H
    obtain ⟨y,hy,he⟩ := H
    exact (ambientEquiv hodd hn b).injective he ▸ hy
  · intro hx
    have H := Set.mem_image_of_mem (ambientEquiv hodd hn b) hx
    rw [adelic_packet_support_eq hodd hn b σ g] at H
    obtain ⟨t,ht⟩ := H
    refine ⟨QuotientGroup.mk t,?_⟩
    change (ambientEquiv hodd hn b).symm _ = x
    exact (congrArg (ambientEquiv hodd hn b).symm ht).trans ((ambientEquiv hodd hn b).symm_apply_apply x)

 

def adelicParametrization {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hodd : Odd (d+1)) (hn : finrank ℚ K = d+1)
    (b : Basis (Fin (d+1)) ℚ K) (σ : OrderedEmbeddings (d+1) K)
    (g : GL (Fin (d+1)) RationalFiniteAdeles) :
    PacketTorusParametrization (TorusQuotient K) (matrixFullLattice hn b g) σ where
  point := adelicTorusPoint hodd hn b σ g
  continuous_point := continuous_adelicTorusPoint hodd hn b σ g
  liftFlow := flowTorus σ hn
  continuous_liftFlow := continuous_flowTorus σ hn
  flow_eq := adelicTorusPoint_flow hodd hn b σ g
  fibers_mul := adelicTorusPoint_fibers_mul hodd hn b σ g
  range_eq := range_adelicTorusPoint hodd hn b σ g

 
theorem adelic_packet_probability {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hodd : Odd (d+1)) (hn : finrank ℚ K = d+1)
    (b : Basis (Fin (d+1)) ℚ K) (σ : OrderedEmbeddings (d+1) K)
    (g : GL (Fin (d+1)) RationalFiniteAdeles) :
    ∃ p : C(TorusQuotient K, X (d+1)),
      (∀ t : (TensorAdeles K)ˣ, ambientEquiv hodd hn b (p (QuotientGroup.mk t)) =
        DoubleCoset.mk (rationalProjectiveGroup (d+1)) (finiteProjectiveIntegral (d+1))
          (adelicRegular b t * (ProjGenLinGroup.mk (realBasisGL hn b σ),ProjGenLinGroup.mk g))) ∧
      ∀ ν : Measure (TorusQuotient K), IsProbabilityMeasure ν → Measure.IsMulLeftInvariant ν →
        Measure.map p ν = packetMeasure (matrixFullLattice hn b g) σ := by
  refine ⟨⟨adelicTorusPoint hodd hn b σ g,continuous_adelicTorusPoint hodd hn b σ g⟩,?_,?_⟩
  · intro t
    exact (ambientEquiv hodd hn b).apply_symm_apply _
  · intro ν hν hInv
    let := hν
    let := hInv
    exact (adelicParametrization hodd hn b σ g).map_invariant_probability hn hodd ν

end PrimeDegreePackets.Adelic

end

end OAI
