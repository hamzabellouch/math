import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianLinearDensity
import OAI.Probability.SKGap.Posterior.GOEObservation
import OAI.Probability.SKGap.Gaussian.GaussianDisintegration

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goeCrossCovariance (r : ℝ) (m : ι → ℝ) : Matrix (ι × ι) ι ℝ :=
  fun p l => r*((if p.1=l then m p.2 else 0)+(if p.2=l then m p.1 else 0))

def goeRegressionCoefficient (r v : ℝ) (m : ι → ℝ) : Matrix (ι × ι) ι ℝ :=
  goeCrossCovariance r m * rankOneCovarianceInverse (r*(m⬝ᵥm)+v) r m

lemma goeCrossCovariance_mulVec (r : ℝ) (m y : ι → ℝ) (i k : ι) :
    (goeCrossCovariance r m*ᵥy) (i,k)=r*(m k*y i+m i*y k) := by
  simp [goeCrossCovariance,mulVec,dotProduct,add_mul,mul_add,Finset.sum_add_distrib,
    mul_assoc]

lemma goeRegressionCoefficient_mulVec (r v : ℝ) (m y : ι → ℝ) (i k : ι) :
    (goeRegressionCoefficient r v m*ᵥy) (i,k) =
      r/(r*(m⬝ᵥm)+v)*(m k*y i+m i*y k)-
      (2*r^2/((r*(m⬝ᵥm)+v)*(v+2*r*(m⬝ᵥm))))*(m⬝ᵥy)*m i*m k := by
  rw [goeRegressionCoefficient,← Matrix.mulVec_mulVec,goeCrossCovariance_mulVec]
  simp only [rankOneCovarianceInverse_mulVec]
  have hden : r*(m⬝ᵥm)+v+r*(m⬝ᵥm)=v+2*r*(m⬝ᵥm) := by ring
  rw [hden]
  ring

lemma goe_observation_cov_matrix {r v : ℝ} (hr : 0 ≤ r) (hv : 0 ≤ v) (m : ι → ℝ) :
    (fun i l => cov[fun g => goeObservation r v m g i,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)])=rankOneCovariance (r*(m⬝ᵥm)+v) r m := by
  ext i l
  rw [goe_observation_cov hr hv]
  simp only [rankOneCovariance,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.vecMulVec_apply,dotProduct,← pow_two]
  ring

lemma goe_regression_covariance {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (m : ι → ℝ)
    (p : ι × ι) (l : ι) :
    cov[fun g => goeMatrix r g p.1 p.2,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)] =
    ∑ k, goeRegressionCoefficient r v m p k *
      cov[fun g => goeObservation r v m g k,fun g => goeObservation r v m g l;
        gaussianCoordinates (MatrixCoordinates ι)] := by
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun k _ => mul_self_nonneg (m k))
  have hs : 0 < r*(m⬝ᵥm)+v := add_pos_of_nonneg_of_pos (mul_nonneg hr hq) hv
  have hS : 0 < r*(m⬝ᵥm)+v+r*(m⬝ᵥm) := add_pos_of_pos_of_nonneg hs (mul_nonneg hr hq)
  have hmat := goe_observation_cov_matrix hr hv.le m
  rw [goe_entry_observation_cov hr]
  change goeCrossCovariance r m p l =
    (goeRegressionCoefficient r v m * (show Matrix ι ι ℝ from fun k l => cov[fun g => goeObservation r v m g k,
      fun g => goeObservation r v m g l;gaussianCoordinates (MatrixCoordinates ι)])) p l
  rw [hmat,goeRegressionCoefficient,Matrix.mul_assoc,
    rankOneCovarianceInverse_mul _ _ _ hs.ne' hS.ne',Matrix.mul_one]

theorem goe_regression_lintegral {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (m : ι → ℝ)
    (F : ((ι × ι) → ℝ) × (ι → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ g, F ((fun p => goeMatrix r g p.1 p.2),goeObservation r v m g) ∂gaussianCoordinates (MatrixCoordinates ι)) =
    ∫⁻ y, ∫⁻ R, F (R+goeRegressionCoefficient r v m*ᵥy,y)
      ∂(gaussianCoordinates (MatrixCoordinates ι)).map (fun g =>
        (fun p => goeMatrix r g p.1 p.2)-goeRegressionCoefficient r v m*ᵥgoeObservation r v m g)
      ∂(gaussianCoordinates (MatrixCoordinates ι)).map (goeObservation r v m) :=
  GaussianRegression.regression_lintegral (goe_observation_joint_gaussian r v m)
    (goeRegressionCoefficient r v m) (goe_regression_covariance hr hv m) F hF

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real GaussianDensity
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma radialDensity_pos {a : ℝ} (ha : 0 < a) (x : ι → ℝ) : 0 < radialDensity a x := by
  unfold radialDensity
  positivity

omit [DecidableEq ι] in
lemma radialDensity_le {a : ℝ} (ha : 0 < a) (x : ι → ℝ) :
    radialDensity a x ≤ ((sqrt (2*Real.pi)*a)⁻¹)^(Fintype.card ι) := by
  unfold radialDensity
  apply mul_le_of_le_one_right (by positivity)
  apply exp_le_one_iff.mpr
  have hx : 0 ≤ x⬝ᵥx := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) (by positivity)

omit [DecidableEq ι] in
lemma continuous_radialDensity (a : ℝ) : Continuous (radialDensity (ι := ι) a) := by
  unfold radialDensity dotProduct
  fun_prop

omit [DecidableEq ι] in
lemma continuous_rankOneDensity (s r : ℝ) (m : ι → ℝ) :
    Continuous (rankOneDensity s r m) := by
  unfold rankOneDensity radialDensity dotProduct
  fun_prop

omit [DecidableEq ι] in
lemma rankOneDensity_pos {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) (m x : ι → ℝ) :
    0 < rankOneDensity s r m x := by
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun i _ => mul_self_nonneg (m i))
  have hS : 0 < s+r*(m⬝ᵥm) := add_pos_of_pos_of_nonneg hs (mul_nonneg hr hq)
  unfold rankOneDensity
  exact mul_pos (mul_pos (sqrt_pos.mpr (div_pos hs hS)) (radialDensity_pos (sqrt_pos.mpr hs) x)) (exp_pos _)

theorem goe_observation_density [Nonempty ι] {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (m : ι → ℝ) :
    (gaussianCoordinates (MatrixCoordinates ι)).map (goeObservation r v m)=
      (volume : Measure (ι → ℝ)).withDensity (fun x =>
        ENNReal.ofReal (rankOneDensity (r*(m⬝ᵥm)+v) r m x)) := by
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun i _ => mul_self_nonneg (m i))
  apply gaussian_rankOne_covariance_density (goe_observation_joint_gaussian r v m).snd
    (add_pos_of_nonneg_of_pos (mul_nonneg hr hq) hv) hr m (goe_observation_mean r v m)
  intro i k
  exact congrFun (congrFun (goe_observation_cov_matrix hr hv.le m) i) k

lemma goe_noise_density [Nonempty ι] {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) :
    (gaussianCoordinates (MatrixCoordinates ι)).map (goeObservation r v 0)=
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (radialDensity (sqrt v) x)) := by
  rw [goe_observation_density hr hv]
  congr 1
  ext x
  simp [rankOneDensity,hv.ne']

lemma goe_noise_independent (r v : ℝ) :
    IndepFun (fun g (p : ι × ι) => goeMatrix r g p.1 p.2) (goeObservation r v 0)
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  apply (goe_observation_joint_gaussian r v 0).indepFun_of_covariance_eval
  intro p i
  have he (g : MatrixCoordinates ι → ℝ) : goeObservation r v 0 g i=sqrt v*g (.inr i) := by
    simp [goeObservation]
  simp only [he,covariance_const_mul_right,goe_noise_cov,mul_zero]

lemma goe_joint_noise_law (r v : ℝ) (m : ι → ℝ) :
    (((gaussianCoordinates (MatrixCoordinates ι)).map (fun g (p : ι × ι) => goeMatrix r g p.1 p.2)).prod
      ((gaussianCoordinates (MatrixCoordinates ι)).map (goeObservation r v 0))).map
      (fun z : ((ι × ι) → ℝ) × (ι → ℝ) => (z.1,(fun i => ∑ k, z.1 (i,k)*m k)+z.2)) =
      (gaussianCoordinates (MatrixCoordinates ι)).map (fun g =>
        ((fun p : ι × ι => goeMatrix r g p.1 p.2),goeObservation r v m g)) := by
  have hXY := goe_observation_joint_gaussian (ι := ι) r v 0
  rw [← (goe_noise_independent (ι := ι) r v).map_prod_eq_prod_map_map hXY.fst.aemeasurable hXY.snd.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hXY.aemeasurable]
  apply congrArg (fun f => (gaussianCoordinates (MatrixCoordinates ι)).map f)
  funext g
  apply Prod.ext
  · rfl
  ext i
  simp [goeObservation,mulVec,dotProduct]

end SKGap
end
end

end OAI
