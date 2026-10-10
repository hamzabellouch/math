import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace Problem336AdditiveD139.GaussianReindex

def reindexCLM {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J] (f : J → I) :
    EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ J :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : J => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => EuclideanSpace.proj (f j))

@[simp] theorem reindexCLM_apply {I : Type u_3} {J : Type u_4} [Fintype I] [Fintype J]
    (f : J → I) (x : EuclideanSpace ℝ I) (j : J) : reindexCLM f x j = x (f j) := rfl

theorem measurePreserving_reindex_multivariateGaussian
    {I : Type u_5} {J : Type u_6} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (f : J → I) (μ : EuclideanSpace ℝ I) (S : Matrix I I ℝ) (hS : S.PosSemidef) :
    MeasurePreserving (reindexCLM f) (multivariateGaussian μ S)
      (multivariateGaussian (reindexCLM f μ) (S.submatrix f f)) where
  measurable := by fun_prop
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun J ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covariance_map]
    · have heval (i : J) : (fun u => ⟪(EuclideanSpace.basisFun J ℝ).toBasis i, u⟫) ∘
          reindexCLM f = fun u => u (f i) := by
        ext u
        simp [PiLp.inner_apply]
      simp_rw [heval, covariance_eval_multivariateGaussian hS,
        covarianceBilin_multivariateGaussian (hS.submatrix _)]
      simp
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

theorem hasLaw_projectiveFamily_reindex
    {Ω : Type u_7} {F : Type u_8} [MeasurableSpace Ω] [Fintype F] [DecidableEq F]
    {P : Measure Ω} {S : Finset ℝ≥0} {X : Ω → S → ℝ}
    (hX : HasLaw X (BrownianReal.projectiveFamily S) P) (f : F → S) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => X ω (f i)))
      (multivariateGaussian 0 (fun i j => min ((f i : S) : ℝ≥0).1 ((f j : S) : ℝ≥0).1)) P := by
  have h1 := (BrownianReal.measurePreserving_toLp_projectiveFamily S).hasLaw.comp hX
  have h2 := (measurePreserving_reindex_multivariateGaussian f 0
    (BrownianReal.covMatrix S) (BrownianReal.posSemidef_covMatrix S)).hasLaw.comp h1
  simp only [Function.comp_def, map_zero] at h2
  convert h2 using 1 <;> rfl

theorem hasLaw_preBrownian_finite_family
    {Ω : Type u_9} {F : Type u_10} [MeasurableSpace Ω] [Fintype F] [DecidableEq F]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (t : F → ℝ≥0) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => B (t i) ω))
      (multivariateGaussian 0 (fun i j => min (t i).1 (t j).1)) P := by
  classical
  let S : Finset ℝ≥0 := Finset.univ.image t
  let f : F → S := fun i => ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  simpa [f, Finset.restrict] using hasLaw_projectiveFamily_reindex (hB.hasLaw S) f

theorem hasLaw_finite_family_of_finset_laws
    {Ω : Type u_11} {T : Type u_12} {F : Type u_13}
    [MeasurableSpace Ω] [DecidableEq T] [Fintype F] [DecidableEq F]
    {P : Measure Ω} (X : T → Ω → ℝ) (K : T → T → ℝ)
    (hK : ∀ S : Finset T, Matrix.PosSemidef (fun i j : S => K i.1 j.1))
    (hX : ∀ S : Finset T, HasLaw (fun ω => WithLp.toLp 2 (S.restrict (X · ω)))
      (multivariateGaussian 0 (fun i j : S => K i.1 j.1)) P)
    (t : F → T) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => X (t i) ω))
      (multivariateGaussian 0 (fun i j => K (t i) (t j))) P := by
  classical
  let S : Finset T := Finset.univ.image t
  let f : F → S := fun i => ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have h := (measurePreserving_reindex_multivariateGaussian f 0
    (fun i j : S => K i.1 j.1) (hK S)).hasLaw.comp (hX S)
  simp only [Function.comp_def, map_zero] at h
  convert h using 1 <;> rfl

theorem hasLaw_time_family_of_finset_laws
    {Ω : Type u_14} {T : Type u_15} {F : Type u_16}
    [MeasurableSpace Ω] [DecidableEq T] [Fintype F] [DecidableEq F]
    {P : Measure Ω} (X : T → Ω → ℝ) (e : T → ℝ≥0)
    (hX : ∀ S : Finset T, HasLaw (fun ω => WithLp.toLp 2 (S.restrict (X · ω)))
      (multivariateGaussian 0 (fun i j : S => min (e i.1).1 (e j.1).1)) P)
    (t : F → T) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => X (t i) ω))
      (multivariateGaussian 0 (fun i j => min (e (t i)).1 (e (t j)).1)) P := by
  classical
  apply hasLaw_finite_family_of_finset_laws X (fun i j => min (e i).1 (e j).1) ?_ hX t
  intro S
  let A : Finset ℝ≥0 := S.image e
  let f : S → A := fun i => ⟨e i.1, Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
  exact (BrownianReal.posSemidef_covMatrix A).submatrix f

end Problem336AdditiveD139.GaussianReindex

end

end OAI
