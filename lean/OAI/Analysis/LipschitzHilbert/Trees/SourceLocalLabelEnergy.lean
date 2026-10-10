import OAI.Analysis.LipschitzHilbert.Trees.SourcePlanarGramSchur
import OAI.Analysis.LipschitzHilbert.Trees.SourceGramGeometry
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlopeLabels

namespace OAI

/-! Equal-length label synthesis uses local angular multiplicity rather
than the total number of labels. Nonneighboring label sums are orthogonal
by their actual Fourier wedges. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem equal_length_label_energy {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (theta : ι → ℝ)
    (ell w cStar cEta CEta : ℝ) (hell : 0<ell) (hw : 0<w) (hcEta : 0<cEta)
    (M Q : ℕ) (hQ : 2*cStar/cEta≤Q)
    (hmultiplicity : SourceSlopeLabels.LocalMultiplicity Finset.univ theta (w/ell) M)
    (hspectrum : ∀ i xi eta, planarAngularFourier (f i) (xi,eta)≠0 →
      |xi+theta i*eta|≤cStar/ell ∧ cEta≤w*eta ∧ w*eta≤CEta) :
    (∫ z, ‖∑ i, f i z‖^2 ∂volume.prod volume)≤
      (((2*Q+1)*M:ℕ):ℝ)*∑ i, ∫ z, ‖f i z‖^2 ∂volume.prod volume := by
  let near := fun i j => |theta i-theta j|≤(2*cStar/cEta)*(w/ell)
  apply planar_sparse_gram_energy f near _ ?_ ?_ ?_
  · intro i j
    dsimp [near]
    rw [abs_sub_comm]
  · intro i
    have hcount := SourceSlopeLabels.window_card_le Finset.univ theta
      (t := theta i) (radius := 2*cStar/cEta) (div_pos hw hell) hmultiplicity hQ
    apply Nat.cast_le.mpr
    convert hcount using 1
    congr 1
    ext j
    simp only [SourceSlopeLabels.window,Finset.mem_filter,Finset.mem_univ,true_and,near]
    rw [abs_sub_comm]
  · intro i j hfar
    by_contra hn
    have hangle := planar_packet_gram_angle (f i) (f j) (theta i) (theta j)
      ell ell w cStar cEta CEta hell hell hw hcEta (hspectrum i) (hspectrum j) hn
    apply hfar
    dsimp [near]
    convert hangle using 1
    ring

end LipschitzHilbert

end

end OAI
