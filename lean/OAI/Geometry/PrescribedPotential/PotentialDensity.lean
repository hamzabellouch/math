import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalOperator

namespace OAI

/-! Potential Density. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Classical Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma hermitian_det_im {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) : H.det.im = 0 := by
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.det.im) hH.eq
  rw [Matrix.det_conjTranspose] at hh
  change -H.det.im = H.det.im at hh
  linarith

namespace KaehlerMetric

def volumePolynomial (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i : Fin A.count) (z : Coordinates d) : ℂ :=
  (g.matrix i z + φ.hessian i z).det / (g.matrix i z).det

lemma volumePolynomial_compatibility (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i j : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    g.volumePolynomial φ i (A.chart i x) = g.volumePolynomial φ j (A.chart j x) := by
  unfold volumePolynomial
  apply (div_eq_div_iff
    (ne_of_gt (g.positive i _ ((A.chart i).mapsTo hi)).det_pos)
    (ne_of_gt (g.positive j _ ((A.chart j).mapsTo hj)).det_pos)).mpr
  rw [g.compatibility i j x hi hj, φ.hessian_compatibility i j hi hj,
    ← add_mul, ← mul_add]
  simp only [Matrix.det_mul]
  ring

lemma volumePolynomial_im (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (g.volumePolynomial φ i z).im = 0 := by
  have hg := (g.positive i z hz).isHermitian
  have hn := hermitian_det_im (hg.add (φ.hessian_hermitian i hz))
  have hd := hermitian_det_im hg
  simp only [volumePolynomial, Complex.div_im, hn, hd, zero_mul, mul_zero,
    sub_zero, zero_div]

lemma volumePolynomial_smooth (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i : Fin A.count) :
    ContDiffOn ℝ ∞ (g.volumePolynomial φ i) (A.chart i).target := by
  exact (MatrixSmoothGeneral.determinant ((g.smooth i).add (φ.hessian_smooth i))).mul
    ((MatrixSmoothGeneral.determinant (g.smooth i)).inv
      (fun z hz => ne_of_gt (g.positive i z hz).det_pos))

def potentialDensityValue (g : KaehlerMetric A) (φ : SmoothRealFunction A) (x : X) : ℝ :=
  (g.volumePolynomial φ (A.covers x).choose (A.chart (A.covers x).choose x)).re

lemma potentialDensityValue_local (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i : Fin A.count) {x : X} (hi : x ∈ (A.chart i).source) :
    g.potentialDensityValue φ x = (g.volumePolynomial φ i (A.chart i x)).re := by
  unfold potentialDensityValue
  rw [g.volumePolynomial_compatibility φ _ i (A.covers x).choose_spec hi]

def potentialDensity (g : KaehlerMetric A) (φ : SmoothRealFunction A) : SmoothRealFunction A where
  value := g.potentialDensityValue φ
  smooth i := by
    apply (Complex.reCLM.contDiff.comp_contDiffOn (g.volumePolynomial_smooth φ i)).congr
    intro z hz
    dsimp only [Function.comp_apply]
    rw [g.potentialDensityValue_local φ i ((A.chart i).mapsTo_symm hz), (A.chart i).right_inv hz]
    rfl

lemma potentialDensity_complex (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i : Fin A.count) {x : X} (hi : x ∈ (A.chart i).source) :
    ((g.potentialDensity φ).value x : ℂ) = g.volumePolynomial φ i (A.chart i x) := by
  apply Complex.ext
  · exact g.potentialDensityValue_local φ i hi
  · exact (g.volumePolynomial_im φ i ((A.chart i).mapsTo hi)).symm

lemma potentialDensity_directional (g : KaehlerMetric A) (φ : SmoothRealFunction A) (x : X) :
    HasDerivAt (fun t : ℝ => (g.potentialDensity (φ.realSMul t)).value x)
      ((g.laplacian φ).value x) 0 := by
  obtain ⟨i, hi⟩ := A.covers x
  let H := g.matrix i (A.chart i x)
  let K := φ.hessian i (A.chart i x)
  have hn : H.det ≠ 0 := ne_of_gt (g.positive i _ ((A.chart i).mapsTo hi)).det_pos
  have hd := ((MongeAmpere.hasDerivAt_det_add_smul H K (isUnit_iff_ne_zero.mpr hn)).div_const H.det).real_of_complex
  have he : H.det * (H⁻¹ * K).trace / H.det = (H⁻¹ * K).trace := by
    rw [mul_div_cancel_left₀ _ hn]
  rw [he] at hd
  have hl : (g.laplacian φ).value x = (H⁻¹ * K).trace.re :=
    g.laplacianValue_local φ i hi
  rw [hl]
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with t
  change g.potentialDensityValue (φ.realSMul t) x = _
  rw [g.potentialDensityValue_local (φ.realSMul t) i hi]
  simp only [volumePolynomial, SmoothRealFunction.hessian_realSMul]
  rfl

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
