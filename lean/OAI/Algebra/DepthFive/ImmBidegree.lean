import OAI.Algebra.DepthFive.ImmDegree
import OAI.Algebra.DepthFive.OperatorRank

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- With a layerwise partition, IMM is already in the selected bidegree. -/
theorem imm_mem_bidegreeSubmodule (K : Type*) [CommSemiring K] (n : ℕ)
    (side : Fin n → Bool) :
    imm K n ∈ bidegreeSubmodule (fun x => side x.1)
      (Finset.univ.filter (fun t => side t = true)).card
      (Finset.univ.filter (fun t => side t = false)).card := by
  classical
  have h := imm_isWeightedHomogeneous K n (bidegreeWeight side)
  have hs : (∑ t, bidegreeWeight side t) =
      ((Finset.univ.filter (fun t => side t = true)).card,
       (Finset.univ.filter (fun t => side t = false)).card) := by
    apply Prod.ext
    · simp only [Prod.fst_sum, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro t ht
      cases hs : side t <;> simp [bidegreeWeight, hs]
    · simp only [Prod.snd_sum, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro t ht
      cases hs : side t <;> simp [bidegreeWeight, hs]
  rw [hs] at h
  exact h

/-- A bidegree projection does not change IMM when the selected index is its layer count. -/
theorem bidegreeComponent_imm (K : Type*) [CommSemiring K] (n : ℕ)
    (side : Fin n → Bool) :
    bidegreeComponent (fun x => side x.1)
      (Finset.univ.filter (fun t => side t = true)).card
      (Finset.univ.filter (fun t => side t = false)).card (imm K n) = imm K n :=
  bidegreeComponent_eq_self (imm_mem_bidegreeSubmodule K n side)

end Problem335

end

end OAI
