import OAI.NumberTheory.SiegelZeros.Differentials.InvariantDerivation
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.BoxPolynomials

namespace OAI

namespace SiegelZeros


namespace W17

variable {K : Type*} [Field K]

theorem invariantDerivation_mem_boxPolynomials (v : Fin 4 → K) {N : ℕ}
    {F : MvPolynomial (Fin 4) K} (hF : F ∈ boxPolynomials K N) :
    WeightedTorusJets.W18.invariantDerivation v F ∈ boxPolynomials K N :=
  WeightedTorusJets.W18.inBox_invariantDerivation v hF

end W17


end SiegelZeros

end OAI
