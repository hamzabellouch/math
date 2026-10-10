import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicQuotientDimension
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GroupDimensionTransport
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeKernelTail

namespace OAI

/-! # Integral dimension through a free abelian quotient -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory

theorem cohomologicalDimension_le_of_lattice_quotient (r : ℕ)
    {G : Type} [Group G] (q : G →* IntegralLatticeGroup r)
    (hq : Function.Surjective q) (d : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral q.ker) d] :
    HasProjectiveDimensionLE (trivialIntegral G) (d + r) := by
  induction r generalizing G with
  | zero =>
    have hker : q.ker = ⊤ := by
      ext g
      exact iff_of_true (Subsingleton.elim (q g) 1) (Subgroup.mem_top g)
    let e := (MulEquiv.subgroupCongr hker).trans Subgroup.topEquiv
    simpa only [Nat.add_zero] using cohomologicalDimension_le_of_equiv e d
  | succ r ih =>
    let p := (latticeCoordinate r).comp q
    obtain ⟨t, ht⟩ := hq (latticeCoordinateSection r)
    have hpt : p t = Multiplicative.ofAdd 1 := by
      change latticeCoordinate r (q t) = _
      rw [ht, latticeCoordinate_section]
    let := integerQuotient_isCyclic p t hpt
    let := integerQuotient_infinite p t hpt
    let := cohomologicalDimension_le_of_equiv (latticeKernelTailEquiv q) d
    let := ih (latticeKernelTail q) (latticeKernelTail_surjective q hq)
    simpa only [Nat.add_assoc] using
      cohomologicalDimension_le_of_infiniteCyclicQuotient p.ker (d + r)

end PolycyclicRecognition

end

end OAI
