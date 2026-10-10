import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedMaskSums
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

namespace OAI

/-! The original finite packet sums and their top-masked versions are
integrable on the full plane. No exceptional set or finite-area bound
is needed for these qualitative facts. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

theorem physicalCrossPacketValue_memLp (p : ℝ≥0∞) (q : P.PacketIndex) :
    MemLp (fun z => P.physicalCrossPacketValue alt hAlt t b v f 0 z q) p (volume.prod volume) := by
  apply memLp_piLp_iff.mpr
  intro k
  have hz (z : ℝ×ℝ) : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp; ring
  have heq (z : ℝ×ℝ) := P.physicalCrossPacketValue_zero alt hAlt t b v f
    (z.2-t*z.1) z.1 q
  simp only [hz] at heq
  have hcomp : (fun z => P.physicalCrossPacketValue alt hAlt t b v f 0 z q k) =
      (fun z => P.physicalMultiplierCoefficient t b v f q.1 q.2.1 q.2.2 k *
        (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k z) := by
    funext z
    exact congrArg (fun u : EuclideanSpace ℂ κ => u k) (heq z)
  rw [hcomp]
  exact ((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).memLp p |>.const_mul _

theorem physicalCrossSum_memLp (p : ℝ≥0∞) (packets : Finset P.PacketIndex) :
    MemLp (fun z => ∑ q ∈ packets, P.physicalCrossPacketValue alt hAlt t b v f 0 z q)
      p (volume.prod volume) := by
  exact memLp_finsetSum _ (fun q _ => P.physicalCrossPacketValue_memLp alt hAlt t b v f p q)

theorem physicalMaskedValue_integrable
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (q : P.PacketIndex) :
    Integrable (fun z => P.physicalMaskedValue alt hAlt t b v f T L A z q) (volume.prod volume) := by
  have hi := (memLp_one_iff_integrable.mp (P.physicalCrossPacketValue_memLp alt hAlt t b v f 1 q))
  apply hi.norm.mono' (P.physicalMaskedValue_continuous alt hAlt t b v f T L A q).aestronglyMeasurable
  filter_upwards [] with z
  rw [P.physicalMaskedValue_eq_cross_at alt hAlt t b v f,norm_smul,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (topSincMask_abs_le_one L A _ _)

theorem physicalMaskedSum_integrable
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (packets : Finset P.PacketIndex) :
    Integrable (fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt t b v f T L A z q)
      (volume.prod volume) := by
  exact integrable_finsetSum _ (fun q _ => P.physicalMaskedValue_integrable alt hAlt t b v f T L A q)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
