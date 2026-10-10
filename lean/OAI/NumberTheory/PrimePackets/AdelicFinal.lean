import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicCanonicalAllowed
import OAI.NumberTheory.PrimePackets.AdelicFinalStatement
import OAI.NumberTheory.PrimePackets.AdelicFull

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set MeasureTheory
namespace PrimeDegreePackets.Adelic

lemma packetOrbits_eq_of_carrier {d : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N : FullLattice (d+1) K} (h : M.carrier = N.carrier) (σ : OrderedEmbeddings (d+1) K) :
    packetOrbits M σ = packetOrbits N σ := by
  unfold packetOrbits LocallyHomothetic completedLattice
  rw [h]

lemma packetMeasure_eq_of_carrier {d : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N : FullLattice (d+1) K} (h : M.carrier = N.carrier) (σ : OrderedEmbeddings (d+1) K) :
    packetMeasure M σ = packetMeasure N σ := by
  unfold packetMeasure orbitBasepoint
  rw [packetOrbits_eq_of_carrier h σ]

lemma packetSupport_eq_of_carrier {d : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N : FullLattice (d+1) K} (h : M.carrier = N.carrier) (σ : OrderedEmbeddings (d+1) K) :
    packetSupport M σ = packetSupport N σ := by
  unfold packetSupport
  rw [packetOrbits_eq_of_carrier h σ]

theorem every_local_type_adelic_realization (d : ℕ) (hprime : (d+1).Prime) (hdegree : 5 ≤ d+1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) (hodd : Odd (d+1)) (b : Basis (Fin (d+1)) ℚ K) :
    EveryLocalTypeAdelicRealization d hprime hdegree K hn hodd b := by
  intro M σ
  obtain ⟨g,hg⟩ := every_full_lattice_occurs hn b M
  have hM : (matrixFullLattice hn b g).carrier = M.carrier := by
    apply SetLike.coe_injective
    exact (matrixFullLattice_carrier hn b g).trans hg
  let p : C(TorusQuotient K, X (d+1)) :=
    ⟨adelicTorusPoint hodd hn b σ g,continuous_adelicTorusPoint hodd hn b σ g⟩
  refine ⟨g,p,hM,canonical_real_diagonalizer_allowed hodd hn b σ,?_,?_,?_⟩
  · intro t
    exact (ambientEquiv hodd hn b).apply_symm_apply _
  · exact (range_adelicTorusPoint hodd hn b σ g).trans (packetSupport_eq_of_carrier hM σ)
  · let := adelicTorusHaar_probability d hprime hdegree K hn
    let := adelicTorusHaar_invariant d hprime hdegree K hn
    exact ((adelicParametrization hodd hn b σ g).map_invariant_probability hn hodd
      (adelicTorusHaar d hprime hdegree K hn)).trans (packetMeasure_eq_of_carrier hM σ)

 

theorem adelic_packet_main (d : ℕ) (hprime : (d+1).Prime) (hdegree : 5 ≤ d+1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) (b : Basis (Fin (d+1)) ℚ K)
    (h : PGL(Fin (d+1), ℝ)) (hh : AllowedRealDiagonalizer b h)
    (g : GL (Fin (d+1)) RationalFiniteAdeles) :
    AdelicPacketTheorem d hprime hdegree K hn (hprime.odd_of_ne_two (by omega)) b h g := by
  exact ⟨adelic_packet d hprime hdegree K hn b h hh g,
    every_local_type_adelic_realization d hprime hdegree K hn _ b,
    canonical_real_diagonalizer_allowed (hprime.odd_of_ne_two (by omega)) hn b⟩

end PrimeDegreePackets.Adelic

end

end OAI
