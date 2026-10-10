import Mathlib
import OAI.Analysis.HardSphere.FormDomain.EnergyInsertionJet
import OAI.Analysis.HardSphere.Geometry.CoordinateLineConsSucc

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.normalized_insertion {n : ℕ} {L : Length} {a C : ℝ}
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (hC : ∀ Y : Configuration n L,
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C)
    {u : Jet n L} (hu : u∈dirichletDomain n L a) :
    f.insertionJet u∈dirichletDomain (n+1) L a ∧
      ‖(f.insertionJet u).1‖=‖u.1‖ ∧ energy (f.insertionJet u)≤energy u+C*‖u.1‖^2 := by
  refine ⟨f.insertionJet_mem_domain hc hu,?_,?_⟩
  · exact f.norm_insertionScalar hn u.1
  · exact f.energy_insertionJet_le hn (f.insertion_orthogonal hr hn) C hC u
end HardSphere

end

end OAI
