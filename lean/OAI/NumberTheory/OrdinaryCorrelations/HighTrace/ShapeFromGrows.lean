import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Nonempty

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
variable {h ℓ : ℕ}

def shapeFromGrows (w : ClosedLine h ℓ) (v : ℤ) (E : Finset (Fin ℓ))
    (hE : Grows w v E) (hne : E.Nonempty) : Shape w where
  top := ⟨v, by
    rw [← grows_min_origin w hE hne]
    exact departure_mem_vertices w _⟩
  edges := ⟨E,mem_erase.mpr ⟨hne.ne_empty,(mem_shapes w v E).mpr hE⟩⟩

lemma Shape.edges_injective (w : ClosedLine h ℓ) :
    Function.Injective (fun Q : Shape w => Q.edges.val) := by
  intro Q R hQR
  have ht : Q.top = R.top := by
    apply Subtype.ext
    rw [← Q.topEdge_origin,← R.topEdge_origin]
    have he : Q.topEdge = R.topEdge := by unfold Shape.topEdge; congr 1
    rw [he]
  cases Q with
  | mk t E =>
    cases R with
    | mk u F =>
      dsimp only at ht hQR
      subst u
      congr 1
      exact Subtype.ext hQR

lemma singleton_grows (w : ClosedLine h ℓ) (e : Fin ℓ) (he : e ∈ w.treeSteps) :
    Grows w (w.offset e.castSucc) {e} := by
  refine ⟨singleton_subset_iff.mpr he,?_⟩
  intro j hj
  exact Or.inl (congrArg (fun i : Fin ℓ => w.offset i.castSucc) (mem_singleton.mp hj))

end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
