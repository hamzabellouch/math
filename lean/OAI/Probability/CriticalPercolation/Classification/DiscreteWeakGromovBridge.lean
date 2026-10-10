import Mathlib
import OAI.Probability.CriticalPercolation.Classification.WeakGromovMainBoundary
import OAI.Probability.CriticalPercolation.Harmonic.WeakGromovHarmonic

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.CompactQuotient
lemma virtuallyNilpotent_of_sparse_word_growth {A : Type*} [Group A]
    (hg : HasSparsePolynomialWordGrowth A) : Group.IsVirtuallyNilpotent A := by
  obtain ⟨S,hSf,h1,hi,hgen,d,hg⟩ := hg
  exact SparseGrowth.sparse_polynomial_virtuallyNilpotent d A
    ⟨S,hSf,h1,hi,hgen,1,by simpa only [one_mul] using hg⟩
end CriticalPercolation.CompactQuotient
namespace CriticalPercolation.GraphTopology
lemma no_weak_Gromov_quotient_counterexample {X : Type*} (Γ : SimpleGraph X) :
    ¬HasWeakGromovQuotientCounterexample Γ := by
  let _ : TopologicalSpace X := ⊥
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  rintro ⟨H,hn,_,_,_,hg,hfail⟩
  let _ := hn
  exact hfail (CompactQuotient.virtuallyNilpotent_of_sparse_word_growth hg)
end CriticalPercolation.GraphTopology

end
end

end OAI
