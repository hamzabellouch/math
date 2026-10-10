import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicChoices
import OAI.NumberTheory.PrimePackets.AdelicFullStatement
import OAI.NumberTheory.PrimePackets.AdelicGeneralPacket

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set MeasureTheory
namespace PrimeDegreePackets.Adelic

 

theorem adelic_packet (d : ℕ) (hprime : (d+1).Prime) (hdegree : 5 ≤ d+1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) (b : Basis (Fin (d+1)) ℚ K)
    (h : PGL(Fin (d+1), ℝ)) (hh : AllowedRealDiagonalizer b h)
    (g : GL (Fin (d+1)) RationalFiniteAdeles) :
    AdelicPacketProposition d hprime hdegree K hn (hprime.odd_of_ne_two (by omega)) b h g := by
  have hodd : Odd (d+1) := hprime.odd_of_ne_two (by omega)
  obtain ⟨σ,p,hp,hrange,hprob⟩ := general_adelic_packet_identification hodd hn b h hh g
  refine ⟨adelic_torus_quotient_compact d hprime hdegree K hn,
    ⟨matrixFullLattice_carrier hn b g,matrixFullLattice_completed hn b g⟩,
    ⟨adelicTorusHaar_probability d hprime hdegree K hn,adelicTorusHaar_isHaar d hprime hdegree K hn⟩,
    ⟨σ,p,hp,hrange,?_⟩,every_full_lattice_occurs hn b,
    (fun m t => generalAdelicOrbit_basis_independent b m h g t),
    (fun g' he t => generalAdelicOrbit_projective_lift_independent b h g g' he t),
    allowed_real_diagonalizer_factorization hn b h hh⟩
  exact hprob _ (adelicTorusHaar_probability d hprime hdegree K hn)
    (adelicTorusHaar_invariant d hprime hdegree K hn)

end PrimeDegreePackets.Adelic

end

end OAI
