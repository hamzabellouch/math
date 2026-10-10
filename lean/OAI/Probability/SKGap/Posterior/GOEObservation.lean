import Mathlib
import OAI.Probability.SKGap.Gaussian.GOEGaussian

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goeObservation (r v : ℝ) (m : ι → ℝ) (g : MatrixCoordinates ι → ℝ) : ι → ℝ :=
  fun i => (goeMatrix r g*ᵥm) i+sqrt v*g (.inr i)

def observationCoeff (r v : ℝ) (m : ι → ℝ) : Matrix ι (MatrixCoordinates ι) ℝ :=
  fun i a => (∑ k, m k*goeEntryCoeff r (i,k) a)+sqrt v*(if a=Sum.inr i then 1 else 0)

lemma observationCoeff_sample (r v : ℝ) (m : ι → ℝ) (g : MatrixCoordinates ι → ℝ) :
    observationCoeff r v m*ᵥg=goeObservation r v m g := by
  ext i
  change (∑ a, ((∑ k, m k*goeEntryCoeff r (i,k) a)+sqrt v*(if a=Sum.inr i then 1 else 0))*g a)=
    (∑ k, goeMatrix r g i k*m k)+sqrt v*g (.inr i)
  rw [show (∑ a, ((∑ k, m k*goeEntryCoeff r (i,k) a)+sqrt v*(if a=Sum.inr i then 1 else 0))*g a)=
    (∑ a, (∑ k, m k*goeEntryCoeff r (i,k) a)*g a)+sqrt v*g (.inr i) by
      simp [add_mul,Finset.sum_add_distrib]]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hh := goeEntryCoeff_sample r g i k
  change (∑ a, m k*goeEntryCoeff r (i,k) a*g a)=goeMatrix r g i k*m k
  rw [show (∑ a, m k*goeEntryCoeff r (i,k) a*g a)=m k*((goeEntryCoeff r*ᵥg) (i,k)) by
    simp only [mulVec,dotProduct,Finset.mul_sum,mul_assoc]]
  rw [hh,mul_comm]

lemma goe_observation_joint_gaussian (r v : ℝ) (m : ι → ℝ) :
    HasGaussianLaw (fun g => ((fun p : ι × ι => goeMatrix r g p.1 p.2),goeObservation r v m g))
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := coordinates_gaussian.map_fun
    ((GaussianRegression.matrixCLM (goeEntryCoeff (ι := ι) r)).prod
      (GaussianRegression.matrixCLM (observationCoeff r v m)))
  apply hh.congr
  filter_upwards [] with g
  simp only [ContinuousLinearMap.prod_apply,GaussianRegression.matrixCLM_apply,
    observationCoeff_sample]
  congr 1
  funext p
  exact goeEntryCoeff_sample r g p.1 p.2

lemma goe_noise_cov (r : ℝ) (i k l : ι) :
    cov[fun g => goeMatrix r g i k,fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0 := by
  have hm (a : MatrixCoordinates ι) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  change cov[fun g : MatrixCoordinates ι → ℝ => sqrt (2*r)/2*(g (.inl (i,k))+g (.inl (k,i))),
    fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0
  rw [covariance_const_mul_left]
  change sqrt (2*r)/2*cov[(fun g => g (.inl (i,k)))+(fun g => g (.inl (k,i))),
    fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0
  rw [covariance_add_left (hm _) (hm _) (hm _)]
  simp [coordinate_covariance]

lemma goe_mulVec_memLp (r : ℝ) (m : ι → ℝ) (i : ι) :
    MemLp (fun g => (goeMatrix r g*ᵥm) i) 2 (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := memLp_finsetSum (Finset.univ : Finset ι)
    (fun k _ => (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two.mul_const (m k))
  simpa only [mulVec,dotProduct] using hh

lemma goe_entry_observation_cov {r : ℝ} (hr : 0 ≤ r) (v : ℝ) (m : ι → ℝ) (i k l : ι) :
    cov[fun g => goeMatrix r g i k,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      r*((if i=l then m k else 0)+(if k=l then m i else 0)) := by
  have hW := (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two
  have hM := goe_mulVec_memLp r m l
  have hN := (coordinate_hasLaw (Sum.inr l : MatrixCoordinates ι)).hasGaussianLaw.memLp_two.const_mul (sqrt v)
  change cov[fun g => goeMatrix r g i k,(fun g => (goeMatrix r g*ᵥm) l)+
    (fun g => sqrt v*g (.inr l));gaussianCoordinates (MatrixCoordinates ι)] = _
  rw [covariance_add_right hW hM hN,covariance_const_mul_right,goe_noise_cov,mul_zero,add_zero]
  change cov[fun g => goeMatrix r g i k,fun g => ∑ a, goeMatrix r g l a*m a;_]=_
  rw [covariance_fun_sum_right (fun a => (goe_matrix_gaussian (ι := ι) r).eval (l,a) |>.memLp_two.mul_const (m a)) hW]
  simp only [covariance_mul_const_right,goe_entry_cov hr]
  by_cases hil : i=l <;> by_cases hkl : k=l <;>
    simp [hil,hkl,mul_add,add_mul,Finset.sum_add_distrib]

lemma goe_mulVec_noise_cov (r : ℝ) (m : ι → ℝ) (i l : ι) :
    cov[fun g => (goeMatrix r g*ᵥm) i,fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0 := by
  change cov[fun g => ∑ a, goeMatrix r g i a*m a,fun g => g (.inr l);_]=_
  rw [covariance_fun_sum_left
    (fun a => (goe_matrix_gaussian (ι := ι) r).eval (i,a) |>.memLp_two.mul_const (m a))
    (coordinate_hasLaw (Sum.inr l : MatrixCoordinates ι)).hasGaussianLaw.memLp_two]
  simp [covariance_mul_const_left,goe_noise_cov]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_mulVec_cov {r : ℝ} (hr : 0 ≤ r) (m : ι → ℝ) (i l : ι) :
    cov[fun g => (goeMatrix r g*ᵥm) i,fun g => (goeMatrix r g*ᵥm) l;
      gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then ∑ k, m k^2 else 0)+m i*m l) := by
  have hc (k : ι) : cov[fun g => goeMatrix r g i k,fun g => (goeMatrix r g*ᵥm) l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      r*((if i=l then m k else 0)+(if k=l then m i else 0)) := by
    simpa only [goeObservation,sqrt_zero,zero_mul,add_zero] using
      goe_entry_observation_cov hr 0 m i k l
  change cov[fun g => ∑ k, goeMatrix r g i k*m k,fun g => (goeMatrix r g*ᵥm) l;_]=_
  rw [covariance_fun_sum_left
    (fun k => (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two.mul_const (m k))
    (goe_mulVec_memLp r m l)]
  simp only [covariance_mul_const_left,hc]
  by_cases h : i=l
  · subst l
    simp [mul_add,add_mul,mul_assoc,← pow_two,Finset.sum_add_distrib,← Finset.mul_sum]
  · simp [h,mul_ite,ite_mul]
    ring

lemma goe_observation_mean (r v : ℝ) (m : ι → ℝ) (i : ι) :
    (∫ g, goeObservation r v m g i ∂gaussianCoordinates (MatrixCoordinates ι))=0 := by
  simpa only [← observationCoeff_sample,mulVec,dotProduct] using
    linear_gaussian_mean (observationCoeff r v m i)

lemma goe_observation_cov {r v : ℝ} (hr : 0 ≤ r) (hv : 0 ≤ v) (m : ι → ℝ) (i l : ι) :
    cov[fun g => goeObservation r v m g i,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      (r*(∑ k,m k^2)+v)*(if i=l then 1 else 0)+r*m i*m l := by
  have hm (k : ι) := goe_mulVec_memLp r m k
  have hn (k : ι) := (coordinate_hasLaw (Sum.inr k : MatrixCoordinates ι)).hasGaussianLaw.memLp_two
  change cov[(fun g => (goeMatrix r g*ᵥm) i)+(fun g => sqrt v*g (.inr i)),
    (fun g => (goeMatrix r g*ᵥm) l)+(fun g => sqrt v*g (.inr l));_]=_
  rw [covariance_add_left (hm i) ((hn i).const_mul _) ((hm l).add ((hn l).const_mul _)),
    covariance_add_right (hm i) (hm l) ((hn l).const_mul _),
    covariance_add_right ((hn i).const_mul _) (hm l) ((hn l).const_mul _)]
  have hback : cov[fun g => g (.inr i),fun g => (goeMatrix r g*ᵥm) l;
      gaussianCoordinates (MatrixCoordinates ι)]=0 := by
    rw [covariance_comm,goe_mulVec_noise_cov]
  rw [covariance_const_mul_right,goe_mulVec_noise_cov,mul_zero,add_zero,
    covariance_const_mul_left,hback,mul_zero,
    covariance_const_mul_left,covariance_const_mul_right,coordinate_covariance,
    goe_mulVec_cov hr]
  simp only [Sum.inr.injEq]
  by_cases hil : i=l
  · simp only [hil,ite_true,mul_one]
    rw [mul_self_sqrt hv]
    ring
  · simp only [hil,ite_false,mul_zero,zero_add,add_zero]
    ring

end SKGap
end
end

end OAI
