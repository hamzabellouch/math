import Mathlib
import OAI.Analysis.AffineBernstein.ModelCenteringFurther
import OAI.Analysis.AffineBernstein.EntireGraphComplete

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LinearNormalizationCalculus

/-- The actual square matrix in the frozen Euclidean coordinates. -/
def cleMatrix {n : ℕ} (A : Space n ≃L[ℝ] Space n) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm A.toContinuousLinearMap

@[simp] lemma cleMatrix_apply {n : ℕ} (A : Space n ≃L[ℝ] Space n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (cleMatrix A) = A.toContinuousLinearMap := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).apply_symm_apply _

lemma cleMatrix_det_ne_zero {n : ℕ} (A : Space n ≃L[ℝ] Space n) : (cleMatrix A).det ≠ 0 := by
  have H : cleMatrix A * cleMatrix A.symm = 1 := by
    apply (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).injective
    simp only [map_mul,map_one]
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (cleMatrix A)) *
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (cleMatrix A.symm)) = 1
    rw [cleMatrix_apply,cleMatrix_apply]
    apply ContinuousLinearMap.ext
    intro x
    exact A.apply_symm_apply x
  have Hd : (cleMatrix A).det * (cleMatrix A.symm).det = 1 := by
    rw [← Matrix.det_mul,H,Matrix.det_one]
  exact left_ne_zero_of_mul_eq_one Hd

/-- Center-preserving horizontal normalization and positive vertical scaling. -/
def normalizedFunction {n : ℕ} (u : Space n → ℝ) (A : Space n ≃L[ℝ] Space n)
    (t : ℝ) (y : Space n) : ℝ := t⁻¹ * u (A y)

lemma normalizedFunction_eq_pullback {n : ℕ} (u : Space n → ℝ)
    (A : Space n ≃L[ℝ] Space n) (t : ℝ) :
    normalizedFunction u A t = affineGraphPullback u (cleMatrix A) 0 0 t⁻¹ 0 := by
  ext y
  simp [normalizedFunction,affineGraphPullback,graphAffineFunction,affineBaseMap]

lemma contDiff_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) :
    ContDiff ℝ ∞ (normalizedFunction u A t) := contDiff_const.mul (hu.comp A.contDiff)

lemma hessian_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (x : Space n) :
    hessian (normalizedFunction u A t) x =
      t⁻¹ • ((cleMatrix A).transpose * hessian u (A x) * cleMatrix A) := by
  rw [normalizedFunction_eq_pullback,hessian_affineGraphPullback isOpen_univ hu.contDiffOn _ _ _ _ _ (mem_univ _)]
  simp only [affineBaseMap,cleMatrix_apply,ContinuousLinearEquiv.coe_coe,add_zero]

lemma posDef_hessian_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (A : Space n ≃L[ℝ] Space n) {t : ℝ} (ht : 0 < t) (x : Space n) :
    (hessian (normalizedFunction u A t) x).PosDef := by
  rw [hessian_normalizedFunction hu]
  exact posDef_affine_congruence (hp _) (cleMatrix_det_ne_zero A) (inv_pos.mpr ht)

lemma affineMaximalOn_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (A : Space n ≃L[ℝ] Space n) {t : ℝ} (ht : 0 < t) :
    AffineMaximalOn univ (normalizedFunction u A t) := by
  rw [normalizedFunction_eq_pullback]
  simpa only [preimage_univ] using affineMaximalOn_affineGraphPullback isOpen_univ hu.contDiffOn
    (fun x _ => hp x) hm (cleMatrix_det_ne_zero A) 0 0 (inv_pos.mpr ht) 0

lemma fderiv_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (x : Space n) :
    fderiv ℝ (normalizedFunction u A t) x = t⁻¹ • ((fderiv ℝ u (A x)).comp A.toContinuousLinearMap) := by
  exact (((hu.differentiable (by simp) (A x)).hasFDerivAt.comp x A.hasFDerivAt).const_mul t⁻¹).fderiv

lemma tangentHeight_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (x y : Space n) :
    tangentHeight (normalizedFunction u A t) x y = t⁻¹ * tangentHeight u (A x) (A y) := by
  simp only [tangentHeight,fderiv_normalizedFunction hu,normalizedFunction,
    smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    map_sub,smul_eq_mul]
  ring

lemma sectionBalance_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    {ρ : ℝ} (hbal : SectionBalance univ u ρ) (A : Space n ≃L[ℝ] Space n)
    {t : ℝ} (ht : 0 < t) : SectionBalance univ (normalizedFunction u A t) ρ := by
  let v := normalizedFunction u A t
  have hv := contDiff_normalizedFunction hu A t
  have hpv := posDef_hessian_normalizedFunction hu hp A ht
  have hcv := euclideanGraphComplete_entire hu
  have hcvv := euclideanGraphComplete_entire hv
  intro x hx s hs y hy
  rw [closure_tangentSection isOpen_univ convex_univ hv.contDiffOn (fun z _ => hpv z) hcvv hx hs] at hy ⊢
  refine ⟨mem_univ _,?_⟩
  have H := (sectionBalance_reflection isOpen_univ convex_univ hu.contDiffOn (fun z _ => hp z)
    hcv hbal (mem_univ (A x)) (mem_univ (A y))).2
  have HH : tangentHeight v x (x-ρ • (y-x)) ≤ tangentHeight v x y := by
    dsimp only [v]
    rw [tangentHeight_normalizedFunction hu,tangentHeight_normalizedFunction hu]
    simp only [map_sub,map_smul]
    exact mul_le_mul_of_nonneg_left H (inv_nonneg.mpr ht.le)
  exact HH.trans hy.2

end LinearNormalizationCalculus


end
end AffineBernstein
end

end OAI
