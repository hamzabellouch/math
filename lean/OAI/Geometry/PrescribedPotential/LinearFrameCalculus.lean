import Mathlib
import OAI.Geometry.PrescribedPotential.MatrixWirtinger

namespace OAI

/-! Linear Frame Calculus. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

def frameMatrix (B : V n →L[ℂ] V n) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' B.toLinearMap

def pullMetric (B : V n →L[ℂ] V n) (M : V n → Matrix (Fin n) (Fin n) ℂ)
    (y : V n) : Matrix (Fin n) (Fin n) ℂ := (frameMatrix B)ᴴ*M (B y)*frameMatrix B

lemma frameMatrix_mulVec (B : V n →L[ℂ] V n) (v : V n) : frameMatrix B*ᵥv = B v :=
  LinearMap.toMatrix'_mulVec B.toLinearMap v

lemma pullMetric_smooth {U : Set (V n)} (hU : IsOpen U)
    (B : V n →L[ℂ] V n) {M : V n → Matrix (Fin n) (Fin n) ℂ}
    (hM : ContDiffOn ℝ ∞ M U) : ContDiffOn ℝ ∞ (pullMetric B M) (B ⁻¹' U) := by
  intro y hy
  have hm := (hM.contDiffAt (hU.mem_nhds hy)).comp y (B.restrictScalars ℝ).contDiff.contDiffAt
  exact (matrix_smooth_mul (matrix_smooth_mul contDiffAt_const hm) contDiffAt_const).contDiffWithinAt

lemma wderiv_comp_linear (B : V n →L[ℂ] V n) {f : V n → ℂ} {z : V n}
    (hf : DifferentiableAt ℝ f (B z)) (a : ℂ) (v : V n) :
    wderiv a v (fun y => f (B y)) z = wderiv a (B v) f (B z) := by
  have he := fderiv_fun_comp z hf (B.restrictScalars ℝ).differentiableAt
  have hb : fderiv ℝ (fun y => B y) z = B.restrictScalars ℝ := (B.restrictScalars ℝ).fderiv
  rw [hb] at he
  simp only [wderiv,he,ContinuousLinearMap.comp_apply]
  change (fderiv ℝ f (B z) (B v) + a*fderiv ℝ f (B z) (B (Complex.I • v)))/2 = _
  rw [map_smul]

lemma mderiv_comp_linear (B : V n →L[ℂ] V n) {M : V n → Matrix (Fin n) (Fin n) ℂ}
    {z : V n} (hM : ContDiffAt ℝ ∞ M (B z)) (a : ℂ) (v : V n) :
    mderiv a v (fun y => M (B y)) z = mderiv a (B v) M (B z) := by
  ext i j
  exact wderiv_comp_linear B ((entry_smooth hM i j).differentiableAt (by simp)) a v

lemma mderiv_congruence {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (C D : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) (v : V n) :
    mderiv a v (fun y => C*M y*D) z = C*mderiv a v M z*D := by
  rw [mderiv_mul (matrix_smooth_mul contDiffAt_const hM) contDiffAt_const,
    mderiv_mul contDiffAt_const hM,mderiv_const,mderiv_const]
  simp only [zero_mul,mul_zero,zero_add,add_zero]

lemma mderiv_pullMetric (B : V n →L[ℂ] V n) {M : V n → Matrix (Fin n) (Fin n) ℂ}
    {z : V n} (hM : ContDiffAt ℝ ∞ M (B z)) (a : ℂ) (v : V n) :
    mderiv a v (pullMetric B M) z =
      (frameMatrix B)ᴴ*mderiv a (B v) M (B z)*frameMatrix B := by
  unfold pullMetric
  rw [mderiv_congruence (show ContDiffAt ℝ ∞ (fun y => M (B y)) z from
    hM.comp z (B.restrictScalars ℝ).contDiff.contDiffAt),
    mderiv_comp_linear B hM]

lemma fundamental_pullMetric (B : V n →L[ℂ] V n)
    (M : V n → Matrix (Fin n) (Fin n) ℂ) (z u v : V n) :
    Anticanonical.ComplexAtlas.fundamentalForm (pullMetric B M z) u v =
      Anticanonical.ComplexAtlas.fundamentalForm (M (B z)) (B u) (B v) := by
  unfold Anticanonical.ComplexAtlas.fundamentalForm pullMetric
  rw [PotentialKaehler.matrix_pair_pullback,frameMatrix_mulVec,frameMatrix_mulVec]

lemma pullMetric_closed {U : Set (V n)} (hU : IsOpen U)
    (B : V n →L[ℂ] V n) {M : V n → Matrix (Fin n) (Fin n) ℂ}
    (hM : ContDiffOn ℝ ∞ M U)
    (hclosed : ∀ y ∈ U, ∀ u v w : V n,
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) v w) y u +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) w u) y v +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) u v) y w = 0) :
    ∀ y ∈ B ⁻¹' U, ∀ u v w : V n,
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (pullMetric B M q) v w) y u +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (pullMetric B M q) w u) y v +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (pullMetric B M q) u v) y w = 0 := by
  intro y hy u v w
  simp only [fundamental_pullMetric]
  have hd (a b : V n) := (Anticanonical.SourceSmooth.fundamentalForm_smooth
    (hM.contDiffAt (hU.mem_nhds hy)) a b).differentiableAt (by simp)
  have hb : fderiv ℝ (fun y => B y) y = B.restrictScalars ℝ := (B.restrictScalars ℝ).fderiv
  simp only [fderiv_fun_comp y (hd _ _) (B.restrictScalars ℝ).differentiableAt,
    hb,ContinuousLinearMap.comp_apply]
  exact hclosed (B y) hy (B u) (B v) (B w)

end KaehlerCalculus

end
end

end OAI
