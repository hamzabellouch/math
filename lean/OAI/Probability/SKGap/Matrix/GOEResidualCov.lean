import Mathlib
import OAI.Probability.SKGap.Matrix.GOERegression
import OAI.Probability.SKGap.Matrix.GOEBilinearCov
import OAI.Probability.SKGap.Gaussian.RegressionMoments

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goeRegressionResidual (r v : ℝ) (m : ι → ℝ) (g : MatrixCoordinates ι → ℝ) : (ι × ι) → ℝ :=
  (fun p => goeMatrix r g p.1 p.2)-goeRegressionCoefficient r v m*ᵥgoeObservation r v m g

lemma goe_cross_row_dot (r : ℝ) (m : ι → ℝ) (l a : ι) :
    m⬝ᵥ(fun b => goeCrossCovariance r m (l,a) b)=2*r*m l*m a := by
  simp only [dotProduct,goeCrossCovariance,mul_add,Finset.sum_add_distrib]
  simp [mul_ite,mul_assoc]
  ring

lemma goeRegressionResidual_cov {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    (m : ι → ℝ) (i k l a : ι) :
    cov[fun g => goeRegressionResidual r v m g (i,k),
      fun g => goeRegressionResidual r v m g (l,a);gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then 1 else 0)*(if k=a then 1 else 0)+(if i=a then 1 else 0)*(if k=l then 1 else 0))-
    r^2/(r*(m⬝ᵥm)+v)*((if i=l then 1 else 0)*m k*m a+(if k=a then 1 else 0)*m i*m l+
      (if i=a then 1 else 0)*m k*m l+(if k=l then 1 else 0)*m i*m a)+
    4*r^3/((r*(m⬝ᵥm)+v)*(v+2*r*(m⬝ᵥm)))*m i*m k*m l*m a := by
  unfold goeRegressionResidual
  rw [GaussianRegression.residual_covariance
    (goe_observation_joint_gaussian r v m) (goeRegressionCoefficient r v m)
    (goe_regression_covariance hr hv m)]
  have hc (b : ι) : cov[fun g => goeObservation r v m g b,
      fun g => goeMatrix r g l a;gaussianCoordinates (MatrixCoordinates ι)] =
      goeCrossCovariance r m (l,a) b := by
    rw [covariance_comm,goe_entry_observation_cov hr]
    rfl
  simp only [hc]
  change cov[fun g => goeMatrix r g i k,fun g => goeMatrix r g l a;_] -
    (goeRegressionCoefficient r v m*ᵥ(fun b => goeCrossCovariance r m (l,a) b)) (i,k)=_
  rw [goe_entry_cov hr,goeRegressionCoefficient_mulVec,goe_cross_row_dot]
  have he (p q : ι) (x : ℝ) : (if p=q then x else 0)=(if q=p then 1 else 0)*x := by
    by_cases hpq : p=q <;> simp [hpq,Ne.symm]
  simp only [goeCrossCovariance]
  rw [he l i (m a),he a i (m l),he l k (m a),he a k (m l)]
  ring

lemma goeRegressionResidual_gaussian (r v : ℝ) (m : ι → ℝ) :
    HasGaussianLaw (goeRegressionResidual r v m) (gaussianCoordinates (MatrixCoordinates ι)) :=
  (GaussianRegression.residual_joint_gaussian (goe_observation_joint_gaussian r v m)
    (goeRegressionCoefficient r v m)).fst

lemma goeRegressionResidual_mean (r v : ℝ) (m : ι → ℝ) (p : ι × ι) :
    (∫ g, goeRegressionResidual r v m g p ∂gaussianCoordinates (MatrixCoordinates ι))=0 := by
  exact GaussianRegression.residual_mean_zero (goe_observation_joint_gaussian r v m)
    (goeRegressionCoefficient r v m) (fun p => goe_mean_zero r p.1 p.2)
    (goe_observation_mean r v m) p

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def blockCoefficient (κ ell : ℝ) (u : ι → ℝ) : Matrix (ι × ι) (ι × ι) ℝ :=
  fun p q => unitRow κ u p.1 q.1*unitRow κ u p.2 q.2+
    ((ell-κ^2)*u p.1*u p.2)*(u q.1*u q.2)

lemma blockCoefficient_sample (r κ ell : ℝ) (u : ι → ℝ) (g : MatrixCoordinates ι → ℝ) :
    blockCoefficient κ ell u*ᵥ(fun p => goeMatrix r g p.1 p.2)=
      fun p => goeBlockResidual r κ ell u g p.1 p.2 := by
  ext p
  simp only [mulVec,dotProduct,blockCoefficient,goeBlockResidual,goeBilinear,
    Fintype.sum_prod_type,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro k _ <;> ring

lemma goeBlockResidual_gaussian (r κ ell : ℝ) (u : ι → ℝ) :
    HasGaussianLaw (fun g (p : ι × ι) => goeBlockResidual r κ ell u g p.1 p.2)
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  exact ((goe_matrix_gaussian (ι := ι) r).map_fun
    (GaussianRegression.matrixCLM (blockCoefficient κ ell u))).congr
      (Filter.Eventually.of_forall (blockCoefficient_sample r κ ell u))

lemma goeBlockResidual_mean (r κ ell : ℝ) (u : ι → ℝ) (p : ι × ι) :
    (∫ g, goeBlockResidual r κ ell u g p.1 p.2 ∂gaussianCoordinates (MatrixCoordinates ι))=0 := by
  have he (g : MatrixCoordinates ι → ℝ) : goeBlockResidual r κ ell u g p.1 p.2=
      (blockCoefficient κ ell u*ᵥ(fun q => goeMatrix r g q.1 q.2)) p :=
    (congrFun (blockCoefficient_sample r κ ell u g) p).symm
  simp only [he,mulVec,dotProduct]
  rw [integral_finsetSum _ (fun q _ => ((goe_matrix_gaussian r).eval q).integrable.const_mul _)]
  simp only [integral_const_mul,goe_mean_zero,mul_zero,Finset.sum_const_zero]

lemma block_regression_cov_algebra {r v c : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) (i k l a : ι) :
    cov[fun g => goeRegressionResidual r v (c • u) g (i,k),
      fun g => goeRegressionResidual r v (c • u) g (l,a);gaussianCoordinates (MatrixCoordinates ι)] =
    cov[fun g => goeBlockResidual r (sqrt (v/(r*c^2+v))) (sqrt (v/(v+2*r*c^2))) u g i k,
      fun g => goeBlockResidual r (sqrt (v/(r*c^2+v))) (sqrt (v/(v+2*r*c^2))) u g l a;
      gaussianCoordinates (MatrixCoordinates ι)] := by
  have hs : 0 < r*c^2+v := add_pos_of_nonneg_of_pos (mul_nonneg hr (sq_nonneg c)) hv
  have hS : 0 < v+2*r*c^2 := add_pos_of_pos_of_nonneg hv (by positivity)
  rw [goeRegressionResidual_cov hr hv,goeBlockResidual_cov hr hu]
  simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul,hu,mul_one,Pi.smul_apply]
  have hq : c*c=c^2 := by ring
  rw [hq,sq_sqrt (div_nonneg hv.le hs.le),sq_sqrt (div_nonneg hv.le hS.le)]
  field_simp
  ring

theorem goe_regression_residual_law {r v c : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) :
    (gaussianCoordinates (MatrixCoordinates ι)).map (goeRegressionResidual r v (c • u))=
    (gaussianCoordinates (MatrixCoordinates ι)).map (fun g p =>
      goeBlockResidual r (sqrt (v/(r*c^2+v))) (sqrt (v/(v+2*r*c^2))) u g p.1 p.2) := by
  apply GaussianRegression.law_eq_of_mean_covariance (goeRegressionResidual_gaussian r v (c • u))
    (goeBlockResidual_gaussian r _ _ u)
  · intro p
    rw [goeRegressionResidual_mean,goeBlockResidual_mean]
  · intro p q
    exact block_regression_cov_algebra hr hv hu p.1 p.2 q.1 q.2

end SKGap
end
end

end OAI
