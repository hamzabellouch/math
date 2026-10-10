import Mathlib
import OAI.Computability.VertexCover.PCP.AlphabetGraphBounds
import OAI.Computability.VertexCover.PCP.AmplificationRound
import OAI.Computability.VertexCover.PCP.GraphGap
import OAI.Computability.VertexCover.PCP.PoweringGap
import OAI.Computability.VertexCover.PCP.PoweringFinalConstants

namespace OAI

                                                                                 

noncomputable section

namespace UniqueGames.Foundations.PCP.RoundGap

open AmplificationRound

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

def poweredLower (epsilon : ℝ) : ℝ :=
  PoweringSoundness.gain (Fintype.card Label) FinalConstants.windowHalf (31 / 32) *
    min (epsilon / (Preprocessing.sizeFactor : ℝ)) FinalConstants.cap

theorem poweredLower_nonnegative (epsilon : ℝ) (he : 0 ≤ epsilon) :
    0 ≤ poweredLower epsilon := by
  have hg := PoweringGap.gain_nonneg (Fintype.card Label)
    FinalConstants.windowHalf (31 / 32) (by norm_num)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  exact mul_nonneg hg (le_min (div_nonneg he hs.le) FinalConstants.cap_positive.le)

theorem powered_count_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label)
    (labeling : Preprocessing.Vertex G → PoweredAlphabet) :
    poweredLower G.gap * (Fintype.card (PoweredDart G) : ℝ) ≤
      ((powered addresses complete G).rejectionCount labeling : ℝ) := by
  let H := Overlay.originalPortGraph (Preprocessing.overlayGraph G)
  have certificate : SpectralReturn.SpectralCertificate
      (PoweringWalks.lazyGraph H) (31 / 32 : ℝ) :=
    Preprocessing.spectral_certificate G
  have lower : ∀ assignment : Preprocessing.Vertex G → Label,
      (G.gap / (Preprocessing.sizeFactor : ℝ)) *
          (Fintype.card (Preprocessing.Vertex G × Preprocessing.Port) : ℝ) ≤
        ((Preprocessing.graph G).rejectionCount assignment : ℝ) :=
    Preprocessing.gap_transfer_real G G.gap G.gap_nonnegative
      ((G.le_gap_iff G.gap).mp le_rfl)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have h := PoweringGap.uniform_count_gap H (31 / 32) certificate
    (Preprocessing.graph G).accepts (Preprocessing.accepts_reverse G)
    FinalConstants.windowHalf FinalConstants.windowHalf_positive
    (selectors addresses complete G)
    (G.gap / (Preprocessing.sizeFactor : ℝ)) (div_nonneg G.gap_nonnegative hs.le)
    lower labeling
  convert h using 1 <;>
    simp only [poweredLower, powered, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq]
  rfl

theorem amplifies (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) :
    min (2 * G.gap) FinalConstants.cap ≤ (graph addresses complete G).gap := by
  apply ((graph addresses complete G).le_gap_iff _).mpr
  intro labeling
  have hcount := AlphabetGraphBounds.gap_transfer_real (powered addresses complete G)
    (poweredLower G.gap) (poweredLower_nonnegative G.gap G.gap_nonnegative)
    (powered_count_gap addresses complete G) labeling
  have hscalar : min (2 * G.gap) FinalConstants.cap ≤ poweredLower G.gap / 12288 := by
    simpa only [poweredLower, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq] using
      PoweringFinalConstants.composed_scaled_gap G.gap G.gap_nonnegative
  exact (mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg _)).trans hcount

end UniqueGames.Foundations.PCP.RoundGap
end

end OAI
