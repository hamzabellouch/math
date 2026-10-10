import OAI.Probability.InvariantIsing.Cavity.CavityGaussianImage
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

namespace OAI

/-! Finite projections of independent Gaussian nodes. Repeated use of a
node retains its covariance, as required by the shared prefixes of replicas. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators RealInnerProductSpace

namespace InvariantIsing

variable {d r : ℕ}

lemma cavity_gaussian_node_coordinate_memLp {J : Type*} [Fintype J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (a : J) (i : Fin d) :
    MemLp (fun z : J → EuclideanSpace ℝ (Fin d) => z a i) 2
      (Measure.pi (fun a => multivariateGaussian 0 (S a))) := by
  have hp := measurePreserving_eval (fun a => multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin d)) (S a)) a
  exact ((IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S a))).map
    (EuclideanSpace.proj i)).memLp_two.comp_measurePreserving hp

lemma cavity_gaussian_node_coordinate_covariance {J : Type*} [Fintype J] [DecidableEq J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ a, (S a).PosSemidef)
    (a b : J) (i j : Fin d) :
    cov[fun z : J → EuclideanSpace ℝ (Fin d) => z a i,
      fun z => z b j; Measure.pi (fun a => multivariateGaussian 0 (S a))] =
        if a = b then S a i j else 0 := by
  by_cases hab : a = b
  · subst b
    rw [ite_eq_left rfl]
    have hp := measurePreserving_eval (fun a => multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (S a)) a
    exact (hp.hasLaw.covariance_fun_comp
      (f := fun x : EuclideanSpace ℝ (Fin d) => x i)
      (g := fun x : EuclideanSpace ℝ (Fin d) => x j)
      (by fun_prop) (by fun_prop)).trans
        (covariance_eval_multivariateGaussian (hS a) i j)
  · rw [ite_eq_right hab]
    have hind := (iIndepFun_pi (μ := fun a => multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (S a)) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hab
    exact (hind.comp (by fun_prop : Measurable (fun x : EuclideanSpace ℝ (Fin d) => x i))
      (by fun_prop : Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j))).covariance_eq_zero
        (cavity_gaussian_node_coordinate_memLp S a i)
        (cavity_gaussian_node_coordinate_memLp S b j)

def cavityGaussianNodeSum {J : Type*} [Fintype J]
    (w : Fin r → J → ℝ) (z : J → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin r × Fin d) :=
  WithLp.toLp 2 (fun p => ∑ a, w p.1 a * z a p.2)

lemma cavity_gaussian_node_sum_hasGaussianLaw {J : Type*} [Fintype J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (w : Fin r → J → ℝ) :
    HasGaussianLaw (cavityGaussianNodeSum (d := d) w)
      (Measure.pi (fun a => multivariateGaussian 0 (S a))) := by
  have hx (a : J) : HasGaussianLaw (fun z : J → EuclideanSpace ℝ (Fin d) => z a)
      (Measure.pi (fun a => multivariateGaussian 0 (S a))) := by
    refine ⟨?_, ?_⟩
    · exact (measurable_pi_apply a).aemeasurable
    · rw [(measurePreserving_eval (fun a => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d)) (S a)) a).map_eq]
      infer_instance
  have hj := (iIndepFun_pi (μ := fun a => multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin d)) (S a)) (X := fun _ => id)
    (fun _ => aemeasurable_id)).hasGaussianLaw hx
  let L : (J → EuclideanSpace ℝ (Fin d)) →L[ℝ] (Fin r × Fin d → ℝ) :=
    ContinuousLinearMap.pi (fun p => ∑ a, w p.1 a •
      ((EuclideanSpace.proj p.2).comp (ContinuousLinearMap.proj a)))
  have hh := (hj.map L).toLp_pi 2
  convert hh using 1
  ext z p
  simp [cavityGaussianNodeSum, L]

lemma cavity_gaussian_node_sum_covariance {J : Type*} [Fintype J] [DecidableEq J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ a, (S a).PosSemidef)
    (w : Fin r → J → ℝ) (p q : Fin r × Fin d) :
    cov[fun z : J → EuclideanSpace ℝ (Fin d) => cavityGaussianNodeSum w z p,
      fun z => cavityGaussianNodeSum w z q;
      Measure.pi (fun a => multivariateGaussian 0 (S a))] =
        ∑ a, w p.1 a * w q.1 a * S a p.2 q.2 := by
  change cov[fun z : J → EuclideanSpace ℝ (Fin d) => ∑ a, w p.1 a * z a p.2,
    fun z => ∑ a, w q.1 a * z a q.2;
    Measure.pi (fun a => multivariateGaussian 0 (S a))] = _
  rw [covariance_fun_sum_fun_sum
    (fun a => (cavity_gaussian_node_coordinate_memLp S a p.2).const_mul _)
    (fun a => (cavity_gaussian_node_coordinate_memLp S a q.2).const_mul _)]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    cavity_gaussian_node_coordinate_covariance S hS]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true]
    ring
  · intro b _ hba
    simp [Ne.symm hba]
  · simp

lemma cavity_gaussian_node_coordinate_mean {J : Type*} [Fintype J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (a : J) (i : Fin d) :
    (∫ z : J → EuclideanSpace ℝ (Fin d), z a i
      ∂Measure.pi (fun a => multivariateGaussian 0 (S a))) = 0 := by
  have hp := measurePreserving_eval (fun a => multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin d)) (S a)) a
  have hmap := hp.hasLaw.integral_comp
    (f := fun x : EuclideanSpace ℝ (Fin d) => x i) (by fun_prop)
  have hm := (EuclideanSpace.proj i).integral_comp_comm
    (IsGaussian.integrable_id (μ := multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (S a)))
  change (∫ x : EuclideanSpace ℝ (Fin d), x i ∂multivariateGaussian 0 (S a)) =
    (∫ x : EuclideanSpace ℝ (Fin d), x ∂multivariateGaussian 0 (S a)) i at hm
  rw [integral_id_multivariateGaussian] at hm
  exact hmap.trans hm

lemma cavity_gaussian_node_sum_mean {J : Type*} [Fintype J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (w : Fin r → J → ℝ) :
    (∫ z, cavityGaussianNodeSum w z
      ∂Measure.pi (fun a => multivariateGaussian 0 (S a))) = 0 := by
  have hy := cavity_gaussian_node_sum_hasGaussianLaw S w
  ext p
  have he := (EuclideanSpace.proj p).integral_comp_comm hy.integrable
  change (∫ z, cavityGaussianNodeSum w z p
    ∂Measure.pi (fun a => multivariateGaussian 0 (S a))) =
      (∫ z, cavityGaussianNodeSum w z
        ∂Measure.pi (fun a => multivariateGaussian 0 (S a))) p at he
  rw [← he]
  change (∫ z : J → EuclideanSpace ℝ (Fin d), ∑ a, w p.1 a * z a p.2
    ∂Measure.pi (fun a => multivariateGaussian 0 (S a))) = 0
  rw [integral_finsetSum _ (fun a _ =>
    ((cavity_gaussian_node_coordinate_memLp S a p.2).const_mul _).integrable (by norm_num))]
  simp_rw [integral_const_mul, cavity_gaussian_node_coordinate_mean, mul_zero]
  exact Finset.sum_const_zero

/-- The covariance of a finite collection of linear node sums determines
its full joint law, including singular covariances. -/
theorem cavity_gaussian_node_sum_law {J : Type*} [Fintype J] [DecidableEq J]
    (S : J → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ a, (S a).PosSemidef)
    (w : Fin r → J → ℝ)
    (Q : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (hQ : Q.PosSemidef)
    (hcov : ∀ p q, Q p q = ∑ a, w p.1 a * w q.1 a * S a p.2 q.2) :
    (Measure.pi (fun a => multivariateGaussian 0 (S a))).map
      (cavityGaussianNodeSum w) = multivariateGaussian 0 Q := by
  let P := Measure.pi (fun a => multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S a))
  let Y := cavityGaussianNodeSum (d := d) w
  have hy := cavity_gaussian_node_sum_hasGaussianLaw S w
  have := hy.isGaussian_map
  apply IsGaussian.ext
  · calc
      (∫ z, z ∂P.map Y) = ∫ z, Y z ∂P :=
        integral_map hy.aemeasurable aestronglyMeasurable_id
      _ = 0 := cavity_gaussian_node_sum_mean S w
      _ = ∫ z, z ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin r × Fin d)) Q :=
        integral_id_multivariateGaussian.symm
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis
      (EuclideanSpace.basisFun (Fin r × Fin d) ℝ).toBasis fun p q => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covarianceBilin_apply_eq_cov]
    · have he (p : Fin r × Fin d) :
          (fun x : EuclideanSpace ℝ (Fin r × Fin d) =>
            inner ℝ ((EuclideanSpace.basisFun (Fin r × Fin d) ℝ).toBasis p) x) =
          fun x => x p := by
        ext x
        simp [PiLp.inner_apply]
      simp_rw [he]
      rw [covariance_map_fun (by fun_prop) (by fun_prop) hy.aemeasurable,
        covariance_eval_multivariateGaussian hQ,
        cavity_gaussian_node_sum_covariance S hS w, hcov]
    · exact IsGaussian.memLp_two_id
    · exact IsGaussian.memLp_two_id

end InvariantIsing

end

end OAI
