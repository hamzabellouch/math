import OAI.Analysis.BoundedHochschild.CompactFamilyAverages

namespace OAI

/-! Relations preserved by every finite average pass to the joint orbit.
These are the linearity and covariance identities of the eventual projection. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {I : Type*}

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma joint_orbit_closed_relation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) (R : Set (I → M → WeakDual ℂ X)) (hR : IsClosed R)
    (hfin : ∀ (n : ℕ) (m : Fin n → M), (∑ j, m j * star (m j) = 1) →
      (fun i => weakOperatorImage e (finiteRightAverage m (T i))) ∈ R) :
    weakFamilyAverageOrbit e T ⊆ R := by
  apply closure_minimal _ hR
  rintro F ⟨n, m, hm, rfl⟩
  exact hfin n m hm

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma weakOperatorImage_complex_smul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (z : ℂ) (T : M →L[ℂ] M) :
    weakOperatorImage e (z • T) = star z • weakOperatorImage e T := by
  funext a
  change StrongDual.toWeakDual (e.symm (z • T a)) = _
  rw [e.symm.map_smulₛₗ]
  rfl

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma joint_orbit_add_relation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) {i j k : I} (hT : T k = T i + T j)
    {F : I → M → WeakDual ℂ X} (hF : F ∈ weakFamilyAverageOrbit e T) :
    F k = F i + F j := by
  apply joint_orbit_closed_relation e T {F | F k = F i + F j} _ _ hF
  · exact isClosed_eq (continuous_apply k) ((continuous_apply i).add (continuous_apply j))
  · intro n m _
    change weakOperatorImage e (finiteRightAverage m (T k)) =
      weakOperatorImage e (finiteRightAverage m (T i)) + weakOperatorImage e (finiteRightAverage m (T j))
    rw [hT, finiteRightAverage_add, weakOperatorImage_add]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma joint_orbit_smul_relation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) {i j : I} (z : ℂ) (hT : T j = z • T i)
    {F : I → M → WeakDual ℂ X} (hF : F ∈ weakFamilyAverageOrbit e T) :
    F j = star z • F i := by
  apply joint_orbit_closed_relation e T {F | F j = star z • F i} _ _ hF
  · exact isClosed_eq (continuous_apply j) ((continuous_apply i).const_smul (star z))
  · intro n m _
    change weakOperatorImage e (finiteRightAverage m (T j)) =
      star z • weakOperatorImage e (finiteRightAverage m (T i))
    rw [hT, finiteRightAverage_smul, weakOperatorImage_complex_smul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma joint_orbit_sandwich_relation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) {i j : I} (a b : M) (hT : T j = leftSandwichMap a b (T i))
    {F : I → M → WeakDual ℂ X} (hF : F ∈ weakFamilyAverageOrbit e T) :
    F j = weakLeftSandwich e a b (F i) := by
  apply joint_orbit_closed_relation e T {F | F j = weakLeftSandwich e a b (F i)} _ _ hF
  · exact isClosed_eq (continuous_apply j)
      ((weakLeftSandwich_continuous e a b).comp (continuous_apply i))
  · intro n m _
    change weakOperatorImage e (finiteRightAverage m (T j)) =
      weakLeftSandwich e a b (weakOperatorImage e (finiteRightAverage m (T i)))
    rw [hT, ← leftSandwichMap_rightAverage, weakLeftSandwich_image]

end BoundedHochschild.KadisonRingrose

end

end OAI
