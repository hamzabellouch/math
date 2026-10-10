import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.OrbitMonomialSymmetric
import OAI.Combinatorics.Chromatic.QuantumTorus.OrdinaryElementaryExpressions
import OAI.Combinatorics.Chromatic.GradedAlgebra.HomogeneousElementaryExpressions

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {σ:Type*} [Fintype σ] {R S:Type*} [CommRing R] [CommRing S]
lemma ElementaryExpr.ordinary_map {N:ℕ} (f:ElementaryExpr N) (φ:R →+* S) :
    MvPolynomial.map φ (f.ordinary (σ:=σ) (R:=R))=f.ordinary (σ:=σ) (R:=S) := by
  induction f with
  | zero=>exact map_zero _
  | one=>exact map_one _
  | atom k=>simp [ordinary,MvPolynomial.esymm]
  | add f g hf hg=>simp only [ordinary,map_add,hf,hg]
  | neg f hf=>simp only [ordinary,map_neg,hf]
  | mul f g hf hg=>simp only [ordinary,map_mul,hf,hg]
end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.OrbitMonomial
open scoped BigOperators
open Classical
noncomputable section
variable {σ:Type*} [Fintype σ] [DecidableEq σ] {R S:Type*} [CommRing R] [CommRing S]
lemma polynomial_map (μ:σ →₀ ℕ) (φ:R →+* S) :
    MvPolynomial.map φ (polynomial μ:MvPolynomial σ R)=(polynomial μ:MvPolynomial σ S) := by
  simp only [polynomial,map_sum,MvPolynomial.map_monomial,map_one]
end
end ElementaryPositivity.OrbitMonomial

end

end OAI
