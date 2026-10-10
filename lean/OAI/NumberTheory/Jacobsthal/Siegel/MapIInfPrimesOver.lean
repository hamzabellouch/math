import Mathlib
import PrimeNumberTheoremAnd.Erdos970.HadamardSupport
import OAI.NumberTheory.Jacobsthal.Siegel.SqrtPairFrobeniusDirections

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
namespace WeightedTorusJets

theorem map_eq_iInf_primesOver
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (P : Ideal R) [P.IsMaximal]
    (hunr : Algebra.IsUnramifiedIn S P) :
    P.map (algebraMap R S) = ⨅ Q : Ideal.primesOver P S, Q.1 := by
  apply le_antisymm
  · refine le_iInf fun Q ↦ ?_
    exact Ideal.map_le_iff_le_comap.mpr Q.2.2.over.le
  · intro x hx
    apply mem_map_of_forall_mem_primesOver P hunr
    intro Q hQ hover
    have hle : (⨅ Q : Ideal.primesOver P S, Q.1) ≤ Q :=
      iInf_le (fun Q : Ideal.primesOver P S ↦ Q.1) ⟨Q, hQ, hover⟩
    exact hle hx

end WeightedTorusJets

end

end Erdos970

end OAI
