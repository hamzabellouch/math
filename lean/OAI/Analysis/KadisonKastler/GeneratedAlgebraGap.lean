import OAI.Analysis.KadisonKastler.PublishedKaplansky
import OAI.Analysis.KadisonKastler.RestrictionGap

namespace OAI

/-! # Gap control under generation and reducing restriction

Kaplansky density supplies bounded test nets. The already constructed
weak-operator limits pass the two near inclusions to the generated
von Neumann algebras without loss in the ordinary gap.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kkDistance_generated_le (hK : PublishedKaplanskyDensity.{u})
    (A B : StarSubalgebra ℂ (H →L[ℂ] H)) :
    kkDistance (generatedVonNeumannAlgebra A) (generatedVonNeumannAlgebra B) ≤
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  apply kkDistance_le_of_weakly_dense_tests _ _ _ _
    (hK.weakUnitBallDense A) (hK.weakUnitBallDense B)
    (Metric.hausdorffDist_nonneg.trans hr.le)
  · intro a
    obtain ⟨b, hb, hab⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
      (show a.val.val ∈ starAlgebraBall A from ⟨a.val.property, a.property⟩)
      hr (starAlgebraBall_hausdorffEDist_ne_top A B)
    exact ⟨b, ⟨subset_generatedVonNeumannAlgebra B hb.1, hb.2⟩,
      by simpa only [dist_eq_norm] using hab.le⟩
  · intro b
    obtain ⟨a, ha, hba⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
      (show b.val.val ∈ starAlgebraBall B from ⟨b.val.property, b.property⟩)
      (show Metric.hausdorffDist (starAlgebraBall B) (starAlgebraBall A) < r by
        simpa only [Metric.hausdorffDist_comm] using hr)
      (starAlgebraBall_hausdorffEDist_ne_top B A)
    exact ⟨a, ⟨subset_generatedVonNeumannAlgebra A ha.1, ha.2⟩,
      by simpa only [dist_eq_norm] using hba.le⟩

theorem kkDistance_generated_restriction_le (hK : PublishedKaplanskyDensity.{u})
    (K : Submodule ℂ H) [CompleteSpace K]
    (A B : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K)
    (hB : ∀ b : B, ∀ x ∈ K, (b : H →L[ℂ] H) x ∈ K)
    (hAc : IsClosed (A : Set (H →L[ℂ] H)))
    (hBc : IsClosed (B : Set (H →L[ℂ] H))) :
    kkDistance (generatedVonNeumannAlgebra (reducingRestriction K A hA).range)
      (generatedVonNeumannAlgebra (reducingRestriction K B hB).range) ≤
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) :=
  (kkDistance_generated_le hK _ _).trans (restriction_gap_le K A B hA hB hAc hBc)

end

end KadisonKastler

end OAI
