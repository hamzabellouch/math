import OAI.Analysis.SphereIsometry.ExtremalPropagation
import OAI.Analysis.SphereIsometry.InvariantConvexSet

namespace OAI

/-!
# The actual closed convex invariant subset of the extremal sphere

The generic positive scheduling theorem is instantiated with the proved
common-support hull growth. No convexity of the full extremal set is assumed.
-/

noncomputable section

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_return_invariant_convex
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (y x₀ : UnitSphere X)
    (t M : ℝ) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (hatt : signedDefect f t x₀ y = M) :
    ∃ C : Set X, C.Nonempty ∧ IsClosed C ∧ Bornology.IsBounded C ∧
      Convex ℝ C ∧ C ⊆ extremalSet f y t ht M ∧
      ContinuousOn (returnAmbient f y t ht) C ∧
      Set.MapsTo (returnAmbient f y t ht) C C := by
  obtain ⟨v₀, hv₀⟩ := extremalSet_nonempty_of_attained f y t ht M x₀ hatt
  have hcont : ContinuousOn (returnAmbient f y t ht) (extremalSet f y t ht M) :=
    (continuousOn_returnAmbient f y t ht).mono
      (fun _ hv => norm_eq_one_of_mem_extremalSet f y t ht M hv)
  obtain ⟨C, hCne, hCc, hCb, hCconv, hCE, hGC⟩ :=
    exists_invariant_closed_convex (returnAmbient f y t ht)
      (extremalSet f y t ht M) v₀ hv₀ (isClosed_extremalSet f y t ht M)
      (fun _ hv => norm_eq_one_of_mem_extremalSet f y t ht M hv) hcont
      (positive_prefix_extension f y t ht M hb)
  exact ⟨C, hCne, hCc, hCb, hCconv, hCE, hcont.mono hCE, hGC⟩

end Tingley

end

end OAI
