import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport

namespace OAI

/-! Global Operator. -/

section

 

noncomputable section
open Matrix Filter Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace MatrixSmoothGeneral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

lemma determinant {U : Set E} {H : E → Matrix (Fin n) (Fin n) ℂ}
    (hH : ContDiffOn ℝ ∞ H U) : ContDiffOn ℝ ∞ (fun z => (H z).det) U := by
  classical
  simp_rw [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro i _
  exact contDiffOn_pi.mp (contDiffOn_pi.mp hH (σ i)) i

lemma adjugate {U : Set E} {H : E → Matrix (Fin n) (Fin n) ℂ}
    (hH : ContDiffOn ℝ ∞ H U) : ContDiffOn ℝ ∞ (fun z => (H z).adjugate) U := by
  classical
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  simp_rw [Matrix.adjugate_apply]
  apply determinant
  apply contDiffOn_pi.mpr
  intro k
  apply contDiffOn_pi.mpr
  intro l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simp only [Matrix.updateRow_ne hk]
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hH k) l

lemma inverse {U : Set E} {H : E → Matrix (Fin n) (Fin n) ℂ}
    (hH : ContDiffOn ℝ ∞ H U) (hh : ∀ x ∈ U, (H x).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun z => (H z)⁻¹) U := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  exact ((determinant hH).inv hh).smul (adjugate hH)
end MatrixSmoothGeneral

namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma transition_det_isUnit (g : KaehlerMetric A) (i j : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    IsUnit (A.derivativeMatrix i j x).det := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  have he := congrArg Matrix.det (g.compatibility i j x hi hj)
  rw [Matrix.det_mul, h, mul_zero] at he
  exact ne_of_gt (g.positive i (A.chart i x) ((A.chart i).mapsTo hi)).det_pos he

lemma linearizedMongeAmpere_compatibility (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i j : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    g.linearizedMongeAmpere φ i (A.chart i x) =
      g.linearizedMongeAmpere φ j (A.chart j x) := by
  let D := A.derivativeMatrix i j x
  have hD : IsUnit D.det := g.transition_det_isUnit i j hi hj
  have hs : IsUnit Dᴴ.det := by rw [det_conjTranspose]; exact hD.star
  unfold linearizedMongeAmpere
  rw [g.compatibility i j x hi hj, φ.hessian_compatibility i j hi hj]
  change (((Dᴴ * g.matrix j (A.chart j x) * D)⁻¹ *
    (Dᴴ * φ.hessian j (A.chart j x) * D)).trace).re = _
  have he : (Dᴴ * g.matrix j (A.chart j x) * D)⁻¹ *
      (Dᴴ * φ.hessian j (A.chart j x) * D) =
      D⁻¹ * (g.matrix j (A.chart j x))⁻¹ * φ.hessian j (A.chart j x) * D := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [mul_assoc, nonsing_inv_mul_cancel_left Dᴴ _ hs]
  rw [he, Matrix.mul_assoc D⁻¹ _ _, trace_mul_cycle, mul_nonsing_inv D hD, one_mul]

 

def laplacianValue (g : KaehlerMetric A) (φ : SmoothRealFunction A) (x : X) : ℝ :=
  g.linearizedMongeAmpere φ (A.covers x).choose (A.chart (A.covers x).choose x)

lemma laplacianValue_local (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i : Fin A.count) {x : X} (hx : x ∈ (A.chart i).source) :
    g.laplacianValue φ x = g.linearizedMongeAmpere φ i (A.chart i x) :=
  g.linearizedMongeAmpere_compatibility φ _ i (A.covers x).choose_spec hx

lemma linearizedMongeAmpere_smooth (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i : Fin A.count) : ContDiffOn ℝ ∞ (g.linearizedMongeAmpere φ i) (A.chart i).target := by
  apply Complex.reCLM.contDiff.comp_contDiffOn
  simp only [Matrix.trace, Matrix.diag_apply]
  apply ContDiffOn.sum
  intro j _
  simp only [Matrix.mul_apply]
  apply ContDiffOn.sum
  intro k _
  apply ContDiffOn.mul
  · exact contDiffOn_pi.mp (contDiffOn_pi.mp
      (MatrixSmoothGeneral.inverse (g.smooth i)
        (fun z hz => ne_of_gt (g.positive i z hz).det_pos)) j) k
  · exact contDiffOn_pi.mp (contDiffOn_pi.mp (φ.hessian_smooth i) k) j

 

def laplacian (g : KaehlerMetric A) (φ : SmoothRealFunction A) : SmoothRealFunction A where
  value := g.laplacianValue φ
  smooth i := by
    apply (g.linearizedMongeAmpere_smooth φ i).congr
    intro z hz
    dsimp only [Function.comp_apply]
    rw [g.laplacianValue_local φ i ((A.chart i).mapsTo_symm hz), (A.chart i).right_inv hz]

lemma laplacian_localExpression (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (g.laplacian φ).localExpression i z = g.linearizedMongeAmpere φ i z := by
  change g.laplacianValue φ ((A.chart i).symm z) = _
  rw [g.laplacianValue_local φ i ((A.chart i).mapsTo_symm hz), (A.chart i).right_inv hz]

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
