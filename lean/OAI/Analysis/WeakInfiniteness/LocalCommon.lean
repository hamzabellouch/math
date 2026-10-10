import Mathlib
import OAI.Analysis.WeakInfiniteness.FiniteComparison
import OAI.Analysis.WeakInfiniteness.LocalConnection2

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology InnerProductSpace

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma exists_local_common_element {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : NonUnitalRepresentationIrreducible π)
    {h k : A} (hh : 0 ≤ h) (hk : 0 ≤ k) (hhn : π h ≠ 0) (hkn : π k ≠ 0) :
    ∃ c : A,0 ≤ c ∧ c ∈ hereditarySubalgebra h hh.isSelfAdjoint ∧ π c ≠ 0 ∧
      CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 h) ∧
      CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 k) := by
  obtain ⟨x,hx,hxx⟩ := exists_orthogonal_detected_family hn hpi π n hh hhn
  obtain ⟨y,hy,hyy⟩ := exists_orthogonal_detected_family hn hpi π n hk hkn
  obtain ⟨d,hd,hdh,hdn,-,hdx⟩ := exists_local_common_family hπ hh hhn x (fun i => (hx i).2)
  obtain ⟨c,hc,hcd,hcn,hccd,hcy⟩ := exists_local_common_family hπ hd hdn y (fun i => (hy i).2)
  refine ⟨c,hc,hereditarySubalgebra_le_of_mem (hereditarySubalgebra_inner h hh.isSelfAdjoint)
    hd.isSelfAdjoint hdh hcd,hcn,?_,?_⟩
  · exact copies_cuntz_of_common_orthogonal hh x (fun i => ⟨(hx i).2.1,(hx i).1⟩)
      hxx (fun i => hccd.trans (hdx i))
  · exact copies_cuntz_of_common_orthogonal hk y (fun i => ⟨(hy i).2.1,(hy i).1⟩) hyy hcy

end

end WeakPureInfiniteness
end

end OAI
