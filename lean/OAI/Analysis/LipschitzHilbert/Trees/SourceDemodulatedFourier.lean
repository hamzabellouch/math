import OAI.Analysis.LipschitzHilbert.Trees.SourceVerticalDemodulation
import OAI.Analysis.LipschitzHilbert.Phase.PlanarSliceFourierAngular
import OAI.Analysis.LipschitzHilbert.Trees.SourceCoordinateSpectrum

namespace OAI

/-! Exact translation of the angular Fourier transform when the
vertical bin carrier is removed. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

theorem planarAngularFourier_vertical_demodulation (f : ℝ×ℝ → ℂ) (nu xi eta : ℝ) :
    planarAngularFourier (fun z => verticalCarrier (-nu) z*f z) (xi,eta)=
      planarAngularFourier f (xi,eta+nu) := by
  simp only [planarAngularFourier_eq_integral,verticalCarrier]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring

theorem planarAngularFourier_verticalDemodulation (nu : κ → ℝ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (k : κ) (xi eta : ℝ) :
    planarAngularFourier (fun z => verticalDemodulation nu f z k) (xi,eta)=
      planarAngularFourier (fun z => f z k) (xi,eta+nu k) := by
  simp_rw [verticalDemodulation_apply]
  exact planarAngularFourier_vertical_demodulation _ _ _ _

/-- A bin of width proportional to 1/W becomes a low vertical-frequency
band; the horizontal bound still uses w and cancels its slope factor. -/
theorem demodulated_packet_bands
    (f : ℝ×ℝ → ℂ) (nu theta ell W w cStar CEta Cb Cv : ℝ)
    (hell : 0<ell) (hw : 0<w) (hCb : 0≤Cb)
    (hslope : |theta|≤Cb*w/ell)
    (hspectrum : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 →
      |xi+theta*eta|≤cStar/ell ∧ |eta|≤CEta/w)
    (hbin : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 → |eta-nu|≤Cv/W) :
    ∀ xi eta, planarAngularFourier (fun z => verticalCarrier (-nu) z*f z) (xi,eta)≠0 →
      |xi|≤(cStar+Cb*CEta)/ell ∧ |eta|≤Cv/W := by
  intro xi eta hne
  rw [planarAngularFourier_vertical_demodulation] at hne
  obtain ⟨hx,hy⟩ := hspectrum xi (eta+nu) hne
  have hv := hbin xi (eta+nu) hne
  constructor
  · calc
      |xi| = |(xi+theta*(eta+nu))-theta*(eta+nu)| := by ring_nf
      _ ≤ |xi+theta*(eta+nu)|+|theta*(eta+nu)| := abs_sub _ _
      _ ≤ cStar/ell+(Cb*w/ell)*(CEta/w) :=
        add_le_add hx (by rw [abs_mul]; exact mul_le_mul hslope hy (abs_nonneg _) (by positivity))
      _ = _ := by field_simp
  · simpa only [add_sub_cancel_right] using hv

/-- Componentwise bin support gives the coordinate slice bounds for the
whole demodulated vector, without a factor for its dimension. -/
theorem verticalDemodulation_coordinate_bands (nu : κ → ℝ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (Rx Ry : ℝ)
    (hf : ∀ k xi eta, planarAngularFourier (fun z => f z k) (xi,eta)≠0 →
      |xi|≤Rx ∧ |eta-nu k|≤Ry) :
    (∀ y xi, 𝓕 (vectorHorizontalSlice (verticalDemodulation nu f) y) xi≠0 →
      |xi|≤Rx/(2*Real.pi)) ∧
    (∀ x eta, 𝓕 (vectorVerticalSlice (verticalDemodulation nu f) x) eta≠0 →
      |eta|≤Ry/(2*Real.pi)) := by
  apply vector_coordinate_fourier_bands
  intro k xi eta hne
  apply planarAngularFourier_coordinate_bands _ Rx Ry _ xi eta hne
  intro a b hb
  change planarAngularFourier (fun z => verticalDemodulation nu f z k) (a,b)≠0 at hb
  rw [planarAngularFourier_verticalDemodulation] at hb
  simpa only [add_sub_cancel_right] using hf k a (b+nu k) hb

end LipschitzHilbert

end

end OAI
