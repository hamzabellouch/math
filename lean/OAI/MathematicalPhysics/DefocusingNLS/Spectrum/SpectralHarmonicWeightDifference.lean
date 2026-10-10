import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicForm
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2WeightDifference

namespace OAI

/-! Uniform mass-weight convergence controls the complete harmonic base form. -/

open MeasureTheory
namespace DefocusingNLS

theorem spectralHarmonicCoordinate_norms (ell : ℕ) (R : ℝ) (u : SpectralHarmonicEnergy ell R) :
    ‖spectralHarmonicValue ell R u‖ ≤ ‖u‖ ∧
    ‖spectralHarmonicDerivative ell R u‖ ≤ ‖u‖ ∧
    ‖spectralHarmonicAngularValue ell R u‖ ≤ ‖u‖ := by
  have h := spectralHarmonicEnergy_norm_sq ell R u
  rw [spectralRadialEnergy_norm_sq] at h
  change ‖u‖^2=‖spectralHarmonicValue ell R u‖^2+
    ‖spectralHarmonicDerivative ell R u‖^2+‖spectralHarmonicAngularValue ell R u‖^2 at h
  constructor
  · nlinarith [norm_nonneg (spectralHarmonicValue ell R u),norm_nonneg u,
      sq_nonneg ‖spectralHarmonicDerivative ell R u‖,sq_nonneg ‖spectralHarmonicAngularValue ell R u‖]
  constructor
  · nlinarith [norm_nonneg (spectralHarmonicDerivative ell R u),norm_nonneg u,
      sq_nonneg ‖spectralHarmonicValue ell R u‖,sq_nonneg ‖spectralHarmonicAngularValue ell R u‖]
  · nlinarith [norm_nonneg (spectralHarmonicAngularValue ell R u),norm_nonneg u,
      sq_nonneg ‖spectralHarmonicValue ell R u‖,sq_nonneg ‖spectralHarmonicDerivative ell R u‖]

theorem spectralHarmonicForm_difference_bound (ell : ℕ) (R : ℝ)
    (w z : SpectralHarmonicWeight R) (δ : ℝ) (hδ : 0 ≤ δ)
    (hr : ∀ᵐ r ∂radialPressureMeasure R, ‖w.density r-z.density r‖ ≤ δ)
    (ha : ∀ᵐ r ∂spectralAngularMeasure R, ‖w.density r-z.density r‖ ≤ δ)
    (u v : SpectralHarmonicEnergy ell R) :
    ‖spectralHarmonicForm ell R w u v-spectralHarmonicForm ell R z u v‖ ≤ 3*δ*‖u‖*‖v‖ := by
  let P := fun q : SpectralHarmonicWeight R => spectralL2Multiplier (radialPressureMeasure R)
    q.density q.radial_measurable q.bound q.radial_bound
  let A := fun q : SpectralHarmonicWeight R => spectralL2Multiplier (spectralAngularMeasure R)
    q.density q.angular_measurable q.bound q.angular_bound
  let V := spectralHarmonicValue ell R
  let D := spectralHarmonicDerivative ell R
  let G := spectralHarmonicAngularValue ell R
  have hV := spectralL2Weight_inner_difference (radialPressureMeasure R) w.density z.density
    w.radial_measurable z.radial_measurable w.bound z.bound w.radial_bound z.radial_bound δ hr (V u) (V v)
  have hD := spectralL2Weight_inner_difference (radialPressureMeasure R) w.density z.density
    w.radial_measurable z.radial_measurable w.bound z.bound w.radial_bound z.radial_bound δ hr (D u) (D v)
  have hG := spectralL2Weight_inner_difference (spectralAngularMeasure R) w.density z.density
    w.angular_measurable z.angular_measurable w.bound z.bound w.angular_bound z.angular_bound δ ha (G u) (G v)
  have hnu := spectralHarmonicCoordinate_norms ell R u
  have hnv := spectralHarmonicCoordinate_norms ell R v
  have hbV : δ*‖V u‖*‖V v‖ ≤ δ*‖u‖*‖v‖ := by gcongr; exact hnu.1; exact hnv.1
  have hbD : δ*‖D u‖*‖D v‖ ≤ δ*‖u‖*‖v‖ := by gcongr; exact hnu.2.1; exact hnv.2.1
  have hbG : δ*‖G u‖*‖G v‖ ≤ δ*‖u‖*‖v‖ := by gcongr; exact hnu.2.2; exact hnv.2.2
  change ‖(inner ℝ (P w (V u)) (V v)+inner ℝ (P w (D u)) (D v)+inner ℝ (A w (G u)) (G v))-
    (inner ℝ (P z (V u)) (V v)+inner ℝ (P z (D u)) (D v)+inner ℝ (A z (G u)) (G v))‖ ≤ _
  have he : (inner ℝ (P w (V u)) (V v)+inner ℝ (P w (D u)) (D v)+inner ℝ (A w (G u)) (G v))-
      (inner ℝ (P z (V u)) (V v)+inner ℝ (P z (D u)) (D v)+inner ℝ (A z (G u)) (G v))=
      (inner ℝ (P w (V u)) (V v)-inner ℝ (P z (V u)) (V v))+
      (inner ℝ (P w (D u)) (D v)-inner ℝ (P z (D u)) (D v))+
      (inner ℝ (A w (G u)) (G v)-inner ℝ (A z (G u)) (G v)) := by ring
  rw [he]
  exact norm_add₃_le.trans (by linarith [hV.trans hbV,hD.trans hbD,hG.trans hbG])

end DefocusingNLS

end OAI
