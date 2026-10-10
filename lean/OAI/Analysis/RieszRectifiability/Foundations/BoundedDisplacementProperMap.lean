import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
A continuous map on a closed Euclidean set is proper when its displacement is uniformly bounded:
preimages of compact sets remain in compact balls of the domain.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem isProperMap_of_bounded_displacement {d : ℕ}
    (A : Set (Ambient d)) (hA : IsClosed A) (hAnonempty : A.Nonempty)
    (f : A → Ambient d) (hf : Continuous f) (B : ℝ)
    (hmove : ∀ u, dist (f u) (u : Ambient d) ≤ B) : IsProperMap f := by
  let : ProperSpace A := ProperSpace.of_isClosed hA
  obtain ⟨a, ha⟩ := hAnonempty
  let a0 : A := ⟨a, ha⟩
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hf, ?_⟩
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall a
  apply (isCompact_closedBall a0 (r + B)).of_isClosed_subset (hK.isClosed.preimage hf)
  intro u hu
  have hnear : dist (f u) a ≤ r := hr hu
  have ht := dist_triangle (u : Ambient d) (f u) a
  rw [dist_comm (u : Ambient d) (f u)] at ht
  have hm := hmove u
  change dist (u : Ambient d) a ≤ r + B
  linarith

theorem isClosed_range_of_bounded_displacement {d : ℕ}
    (A : Set (Ambient d)) (hA : IsClosed A) (hAnonempty : A.Nonempty)
    (f : A → Ambient d) (hf : Continuous f) (B : ℝ)
    (hmove : ∀ u, dist (f u) (u : Ambient d) ≤ B) : IsClosed (Set.range f) := by
  have hp := isProperMap_of_bounded_displacement A hA hAnonempty f hf B hmove
  simpa only [Set.image_univ] using! hp.isClosedMap Set.univ isClosed_univ

end

end RieszRectifiability

end OAI
