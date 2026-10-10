import OAI.Algebra.AffineCancellation.GradedLND

namespace OAI

noncomputable section

namespace ComplexCancellation.GradedLND
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (G : ℤ → Submodule k R) [GradedAlgebra G]
lemma linear_projection (H : R →ₗ[k] R) (hH : ∀ i r, r ∈ G i → H r ∈ G i) (i : ℤ) (r : R) :
    H (proj G i r)=proj G i (H r) := by
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => simp only [map_zero]
  | @homogeneous j r =>
    by_cases hj : j=i
    · subst j
      rw [proj_of_mem G r.2,proj_of_mem G (hH i r r.2)]
    · rw [proj_of_mem_ne G r.2 hj,proj_of_mem_ne G (hH j r r.2) hj,map_zero]
  | add r s hr hs => simp only [map_add,hr,hs]
lemma component_commute (D H : Derivation k R R) (hH : ∀ i r, r ∈ G i → H r ∈ G i)
    (hc : ∀ r, H (D r)=D (H r)) (j : ℤ) (r : R) :
    H (component G D j r)=component G D j (H r) := by
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => simp only [map_zero]
  | @homogeneous i r =>
    rw [component_of_mem G D j r.2,component_of_mem G D j (hH i r r.2)]
    exact (linear_projection G H.toLinearMap hH (i+j) (D r)).trans (congrArg (proj G (i+j)) (hc r))
  | add r s hr hs => simp only [map_add,hr,hs]
end ComplexCancellation.GradedLND

end

end OAI
