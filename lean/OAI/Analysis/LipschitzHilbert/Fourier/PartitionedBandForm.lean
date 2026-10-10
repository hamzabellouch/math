import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedAnnularForm
import OAI.Analysis.LipschitzHilbert.Fourier.RectangularFrequencyCutoff
import OAI.Analysis.LipschitzHilbert.Trees.SlopePartitionGrid

namespace OAI

/-! Remove the two auxiliary frequency plateaus from the actual
partitioned multiplier. They equal one on its contributing frequencies. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

def finitePartitionedBand (psi rho beta : SchwartzMap ℝ ℂ)
    (topLength width w : ℝ) (labels : ∀ j, Finset (Label j))
    (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (u : ℝ×ℝ → ℝ) (f : κ → SchwartzMap (ℝ×ℝ) ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) : ℂ :=
  ∑ i : LatticeRow labels, ∑ k, ∫ z,
    (∫ omega, Real.fourierChar (z.1*omega.1+z.2*omega.2) •
      (psi (latticeLength topLength labels i*(omega.1+u z*omega.2))*
        rho (-symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2)/(w*omega.2))*
        beta (symbolY width omega.2 (center k))*planarFourier (f k) omega) ∂planeMeasure)*
      star (g z k) ∂planeMeasure

theorem partitionedAnnularSum_eq_finitePartitionedBand
    (psi beta : SchwartzMap ℝ ℂ) (A B c C delta : ℝ)
    (hA : 0<A) (hB : 0<B) (hc : 0<c) (hdelta : 0<delta) (hnarrow : delta*C≤A/2)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2)
    (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width) (hw : 0<w)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (hlo : ∀ k, c+B*(w/width)≤w*center k)
    (hhi : ∀ k, w*center k+B*(w/width)≤C)
    (u : ℝ×ℝ → ℝ) (f : κ → SchwartzMap (ℝ×ℝ) ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    partitionedAnnularSum psi (scaledSlopePartition delta hdelta) beta
      (rectangularFrequencyCutoff A B hA hB) (rectangularFrequencyCutoff A B hA hB)
      topLength width w htop hwidth labels theta center u f g=
      finitePartitionedBand psi (scaledSlopePartition delta hdelta) beta topLength width w
        labels theta center u f g := by
  classical
  unfold partitionedAnnularSum finitePartitionedBand
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  apply integral_congr_ae
  filter_upwards [] with omega
  by_cases hb : beta (symbolY width omega.2 (center k))=0
  · simp only [hb,mul_zero,zero_mul,smul_zero]
  by_cases hr : scaledSlopePartition delta hdelta
      (-symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2)/(w*omega.2))=0
  · simp only [hr,mul_zero,zero_mul,smul_zero]
  have hY := hbeta _ hb
  have hY' : |symbolY width omega.2 (center k)|≤B := hY.trans (by linarith)
  obtain ⟨hVlo,hVhi⟩ := vertical_annulus_from_window w width (center k) omega.2 B c C
    hw hwidth (hlo k) (hhi k) hY'
  have hVp : 0<w*omega.2 := hc.trans_le hVlo
  have hX := scaledSlopePartition_support delta hdelta _ hr
  rw [abs_div,abs_neg,abs_of_pos hVp] at hX
  have hX' : |symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2)|≤A/2 :=
    ((div_le_iff₀ hVp).mp hX).trans ((mul_le_mul_of_nonneg_left hVhi hdelta.le).trans hnarrow)
  have hwindow : latticeFrequencyWindow (rectangularFrequencyCutoff A B hA hB)
      topLength width htop hwidth labels theta center i k omega=1 := by
    rw [show latticeFrequencyWindow (rectangularFrequencyCutoff A B hA hB)
      topLength width htop hwidth labels theta center i k omega=
      rectangularFrequencyCutoff A B hA hB
        (symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2),
          symbolY width omega.2 (center k)) from
      scaledWindow_inverse_profile_apply _ _ width _ _
        (latticeLength_pos topLength htop labels i) hwidth omega.1 omega.2]
    exact rectangularFrequencyCutoff_one A B hA hB _ hX' hY
  simp only [hwindow,one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
