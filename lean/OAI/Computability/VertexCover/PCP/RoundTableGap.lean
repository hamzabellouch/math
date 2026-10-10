import Mathlib
import OAI.Computability.VertexCover.PCP.RoundTables
import OAI.Computability.VertexCover.PCP.RoundGap
import OAI.Computability.VertexCover.PCP.PoweringPortReindex

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.RoundTableGap

open RoundTables
open PoweringWalks SpectralReturn

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem powered_count_gap (input : Input)
    (labeling : Fin (powered H input.val).vertices → Fin alphabet) :
    RoundGap.poweredLower (gap input) * ((powered H input.val).darts : ℝ) ≤
      ((GenericGraphTables.semantics (powered H input.val)).rejectionCount labeling : ℝ) := by
  let old := PreprocessingOverlayTables.overlay
    (PreprocessingTables.padded H input.val) (PreprocessingTables.overlayFamily H input.val)
  have hd : 0 < (PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree := by omega
  let : Nonempty (Fin ((PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree)) := ⟨⟨0, hd⟩⟩
  have spectral : SpectralCertificate (lazyGraph (PortTables.portGraph old)) (31 / 32 : ℝ) :=
    LazySpectral.lazy_certificate_31_32 (PortTables.portGraph old)
      (PreprocessingGuarantees.overlay_certificate H certificate input.val)
  have lower := PreprocessingGuarantees.gap_transfer_real H certificate input.val input.property
    (gap input) (gap_nonnegative input)
    (by simpa only [Fintype.card_fin] using
      ((GraphTables.semantics input.val).le_gap_iff (gap input)).mp le_rfl)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := Nat.cast_pos.mpr Preprocessing.sizeFactor_positive
  have hn : walkParameter = 2 * PoweringSoundness.center 64 FinalConstants.windowHalf :=
    walkParameter_eq
  have bound := PoweringPortReindex.lazy_table_uniform_count_gap_at old
    (PreprocessingTables.vertices_positive input.val) hd (31 / 32) spectral
    FinalConstants.windowHalf FinalConstants.windowHalf_positive walkParameter hn
    (gap input / Preprocessing.sizeFactor) (div_nonneg (gap_nonnegative input) hs.le)
    lower labeling
  have hw : walkParameter + 1 = FinalConstants.walkLength := by
    rw [walkParameter_eq]
    rfl
  simp only [RoundGap.poweredLower, PoweringFinalConstants.card_alphabet,
    hw, FinalConstants.cap, powered, PreprocessingTables.preprocess, old] at bound ⊢
  exact bound

theorem build_count_gap (input : Input)
    (labeling : Fin (build H input.val).vertices → GraphTables.Label) :
    min (2 * gap input) FinalConstants.cap * ((build H input.val).darts : ℝ) ≤
      ((GraphTables.semantics (build H input.val)).rejectionCount labeling : ℝ) := by
  have h := AlphabetTableBounds.gap_transfer_real alphabet_positive (powered H input.val)
    (RoundGap.poweredLower (gap input))
    (RoundGap.poweredLower_nonnegative (gap input) (gap_nonnegative input))
    (powered_count_gap H certificate input) labeling
  have scalar : min (2 * gap input) FinalConstants.cap ≤
      RoundGap.poweredLower (gap input) / 12288 := by
    simpa only [RoundGap.poweredLower, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq] using
      PoweringFinalConstants.composed_scaled_gap (gap input) (gap_nonnegative input)
  exact (mul_le_mul_of_nonneg_right scalar (Nat.cast_nonneg _)).trans h

theorem step_gap (input : Input) :
    min (2 * gap input) FinalConstants.cap ≤ gap (step H input) := by
  apply ((GraphTables.semantics (step H input).val).le_gap_iff _).mpr
  intro labeling
  rw [Fintype.card_fin]
  exact build_count_gap H certificate input labeling

end UniqueGames.Foundations.PCP.RoundTableGap

end OAI
