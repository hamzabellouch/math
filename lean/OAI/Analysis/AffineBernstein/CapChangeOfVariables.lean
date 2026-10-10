import Mathlib
import OAI.Analysis.AffineBernstein.CapCoordinates

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

def graphAmbientBasis (n : ℕ) : Module.Basis (Fin n ⊕ Unit) ℝ (Space n × ℝ) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.prod (Module.Basis.singleton Unit ℝ)

lemma determinant_triangular {n : ℕ}
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) :
    M.toContinuousLinearMap.det = (triangularBaseEquiv M hc hcn).toContinuousLinearMap.det*c := by
  change LinearMap.det M.toLinearEquiv.toLinearMap = _
  rw [← LinearMap.det_toMatrix (graphAmbientBasis n)]
  have he : LinearMap.toMatrix (graphAmbientBasis n) (graphAmbientBasis n) M.toLinearEquiv.toLinearMap =
      Matrix.fromBlocks (equivMatrix (triangularBaseEquiv M hc hcn)) 0
        (Matrix.of fun (_ : Unit) j => (M ((EuclideanSpace.basisFun (Fin n) ℝ) j,0)).2)
        (Matrix.of fun (_ _ : Unit) => c) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,equivMatrix,
        Matrix.fromBlocks,triangularBaseEquiv_apply]
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks,hc]
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks]
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks,hc]
  rw [he,Matrix.det_fromBlocks_zero₁₂,equivMatrix_det,Matrix.det_unique]
  rfl

lemma det_verticalShear {n : ℕ} (p : Space n) :
    (verticalShear p).toContinuousLinearMap.det = 1 := by
  change LinearMap.det (verticalShear p).toLinearEquiv.toLinearMap = _
  rw [← LinearMap.det_toMatrix (graphAmbientBasis n)]
  have he : LinearMap.toMatrix (graphAmbientBasis n) (graphAmbientBasis n)
      (verticalShear p).toLinearEquiv.toLinearMap =
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ)
        (Matrix.of fun i (_ : Unit) => -p i) 0 (1 : Matrix Unit Unit ℝ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks,Matrix.one_apply]
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks]
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks]
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks]
  rw [he,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,Matrix.det_one,mul_one]

lemma affineAreaDensity_cleGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (B : Space n ≃L[ℝ] Space n) (d : Space n) (a : Space n →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (e : ℝ) {x : Space n} (hx : B x+d ∈ Ω) :
    affineAreaDensity (cleGraphPullback u B d a c e) x =
      Real.rpow (c^n*(equivMatrix B).det^2) (1/((n:ℝ)+2))*affineAreaDensity u (B x+d) := by
  have he : affineBaseMap (equivMatrix B) d x = B x+d := by
    simp [affineBaseMap,toEuclideanCLM_equivMatrix]
  rw [cleGraphPullback_eq,affineAreaDensity,
    hessian_affineGraphPullback hΩ hu (equivMatrix B) d a c e (he ▸ hx),
    det_affine_congruence,he]
  exact Real.mul_rpow (mul_nonneg (pow_nonneg hc.le _) (sq_nonneg _)) (hp _ hx).det_pos.le

lemma integral_affine_base_preimage {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    (d : Space n) {E : Set (Space n)} (hE : MeasurableSet E) (f : Space n → ℝ) :
    (∫ x in E, f x) = |B.toContinuousLinearMap.det| *
      ∫ y in {y | B y+d ∈ E}, f (B y+d) := by
  have hc : Continuous (fun y => B y+d) := B.continuous.add_const d
  have himg : (fun y => B y+d) '' {y | B y+d ∈ E} = E := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx; exact ⟨B.symm (x-d),by simpa using hx,by simp⟩
  have hi := integral_image_eq_integral_abs_det_fderiv_smul (s := {y | B y+d ∈ E})
    (f := fun y => B y+d) (f' := fun _ => B.toContinuousLinearMap)
    volume (hE.preimage hc.measurable)
    (fun y hy => (B.hasFDerivAt.add_const d).hasFDerivWithinAt)
    (fun y hy z hz he => B.injective (add_right_cancel he)) f
  simpa only [himg,smul_eq_mul,integral_const_mul] using hi

lemma affine_area_pullback_integral {n : ℕ} {Ω E : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hE : MeasurableSet E) (hEΩ : E ⊆ Ω)
    (B : Space n ≃L[ℝ] Space n) (d : Space n) (a : Space n →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (e : ℝ) :
    |(equivMatrix B).det| * (∫ y in {y | B y+d ∈ E},
        affineAreaDensity (cleGraphPullback u B d a c e) y) =
      Real.rpow (c^n*(equivMatrix B).det^2) (1/((n:ℝ)+2)) *
        ∫ x in E, affineAreaDensity u x := by
  have hm : MeasurableSet {y | B y+d ∈ E} :=
    hE.preimage (B.continuous.add_const d).measurable
  have hi : (∫ y in {y | B y+d ∈ E}, affineAreaDensity (cleGraphPullback u B d a c e) y) =
      Real.rpow (c^n*(equivMatrix B).det^2) (1/((n:ℝ)+2)) *
        ∫ y in {y | B y+d ∈ E}, affineAreaDensity u (B y+d) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hm
    intro y hy
    exact affineAreaDensity_cleGraphPullback hΩ hu hp B d a hc e (hEΩ hy)
  rw [hi,integral_affine_base_preimage B d hE,equivMatrix_det]
  ring

end AffineBernstein
end

end OAI
