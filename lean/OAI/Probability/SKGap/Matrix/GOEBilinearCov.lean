import Mathlib
import OAI.Probability.SKGap.Posterior.GOEObservation

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_entry_mulVec_cov {r : ℝ} (hr : 0 ≤ r) (v : ι → ℝ) (i k l : ι) :
    cov[fun g => goeMatrix r g i k,fun g => (goeMatrix r g*ᵥv) l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      r*((if i=l then v k else 0)+(if k=l then v i else 0)) := by
  simpa only [goeObservation,sqrt_zero,zero_mul,add_zero] using
    goe_entry_observation_cov hr 0 v i k l

lemma goe_mulVec_cross_cov {r : ℝ} (hr : 0 ≤ r) (u v : ι → ℝ) (i l : ι) :
    cov[fun g => (goeMatrix r g*ᵥu) i,fun g => (goeMatrix r g*ᵥv) l;
      gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then u⬝ᵥv else 0)+v i*u l) := by
  change cov[fun g => ∑ k,goeMatrix r g i k*u k,fun g => (goeMatrix r g*ᵥv) l;_]=_
  rw [covariance_fun_sum_left
    (fun k => (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two.mul_const (u k))
    (goe_mulVec_memLp r v l)]
  simp only [covariance_mul_const_left,goe_entry_mulVec_cov hr]
  by_cases hil : i=l
  · subst l
    simp only [ite_true,mul_add,add_mul,Finset.sum_add_distrib]
    have hsum : (∑ k,r*v k*u k)=r*(u⬝ᵥv) := by
      simp only [dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsum]
    simp [mul_ite,ite_mul,mul_assoc]
  · simp [hil,mul_ite,ite_mul]
    ring

def goeBilinear (r : ℝ) (x y : ι → ℝ) (g : MatrixCoordinates ι → ℝ) : ℝ :=
  x⬝ᵥ(goeMatrix r g*ᵥy)

lemma goeBilinear_memLp (r : ℝ) (x y : ι → ℝ) :
    MemLp (goeBilinear r x y) 2 (gaussianCoordinates (MatrixCoordinates ι)) := by
  exact memLp_finsetSum _ (fun i _ => (goe_mulVec_memLp r y i).const_mul (x i))

lemma goe_bilinear_cov {r : ℝ} (hr : 0 ≤ r) (x y u v : ι → ℝ) :
    cov[goeBilinear r x y,goeBilinear r u v;gaussianCoordinates (MatrixCoordinates ι)] =
    r*((x⬝ᵥu)*(y⬝ᵥv)+(x⬝ᵥv)*(y⬝ᵥu)) := by
  change cov[fun g => ∑ i,x i*(goeMatrix r g*ᵥy) i,
    fun g => ∑ k,u k*(goeMatrix r g*ᵥv) k;_]=_
  rw [covariance_fun_sum_fun_sum (fun i => (goe_mulVec_memLp r y i).const_mul (x i))
    (fun k => (goe_mulVec_memLp r v k).const_mul (u k))]
  simp only [covariance_const_mul_left,covariance_const_mul_right,goe_mulVec_cross_cov hr]
  have hsum (i : ι) : (∑ k,u k*(x i*(r*((if i=k then y⬝ᵥv else 0)+v i*y k))))=
      r*((x i*u i)*(y⬝ᵥv)+(x i*v i)*(y⬝ᵥu)) := by
    simp only [mul_add,Finset.sum_add_distrib]
    have hf : (∑ k,u k*(x i*(r*(v i*y k))))=(r*(x i*v i))*(y⬝ᵥu) := by
      simp only [dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hf]
    simp [mul_ite]
    ring
  simp_rw [hsum]
  simp only [mul_add,Finset.sum_add_distrib]
  have h1 : (∑ i,r*((x i*u i)*(y⬝ᵥv)))=r*((x⬝ᵥu)*(y⬝ᵥv)) := by
    rw [← Finset.mul_sum,← Finset.sum_mul]
    rfl
  have h2 : (∑ i,r*((x i*v i)*(y⬝ᵥu)))=r*((x⬝ᵥv)*(y⬝ᵥu)) := by
    rw [← Finset.mul_sum,← Finset.sum_mul]
    rfl
  rw [h1,h2]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def unitRow (κ : ℝ) (u : ι → ℝ) (i : ι) : ι → ℝ :=
  Pi.single i 1+((κ-1)*u i) • u

lemma unitRow_dot {u : ι → ℝ} (hu : u⬝ᵥu=1) (κ : ℝ) (i : ι) :
    unitRow κ u i⬝ᵥu=κ*u i := by
  simp only [unitRow,add_dotProduct,single_one_dotProduct,smul_dotProduct,hu,smul_eq_mul,mul_one]
  ring

lemma unitRow_dot_unitRow {u : ι → ℝ} (hu : u⬝ᵥu=1) (κ : ℝ) (i l : ι) :
    unitRow κ u i⬝ᵥunitRow κ u l=(if i=l then 1 else 0)+(κ^2-1)*u i*u l := by
  simp only [unitRow,add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,
    single_one_dotProduct,dotProduct_single_one,hu,smul_eq_mul,mul_one]
  by_cases hil : i=l <;> simp [hil] <;> ring

def goeBlockResidual (r κ ell : ℝ) (u : ι → ℝ) (g : MatrixCoordinates ι → ℝ) : Matrix ι ι ℝ :=
  fun i k => goeBilinear r (unitRow κ u i) (unitRow κ u k) g+
    ((ell-κ^2)*u i*u k)*goeBilinear r u u g

lemma goeBlockResidual_memLp (r κ ell : ℝ) (u : ι → ℝ) (i k : ι) :
    MemLp (fun g => goeBlockResidual r κ ell u g i k) 2 (gaussianCoordinates (MatrixCoordinates ι)) :=
  (goeBilinear_memLp r _ _).add ((goeBilinear_memLp r u u).const_mul _)

lemma goeBlockResidual_cov {r : ℝ} (hr : 0 ≤ r) {u : ι → ℝ} (hu : u⬝ᵥu=1)
    (κ ell : ℝ) (i k l a : ι) :
    cov[fun g => goeBlockResidual r κ ell u g i k,
      fun g => goeBlockResidual r κ ell u g l a;gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then 1 else 0)*(if k=a then 1 else 0)+(if i=a then 1 else 0)*(if k=l then 1 else 0))+
    r*(κ^2-1)*((if i=l then 1 else 0)*u k*u a+(if k=a then 1 else 0)*u i*u l+
      (if i=a then 1 else 0)*u k*u l+(if k=l then 1 else 0)*u i*u a)+
    2*r*(ell^2-2*κ^2+1)*u i*u k*u l*u a := by
  have hB (i k : ι) := goeBilinear_memLp r (unitRow κ u i) (unitRow κ u k)
  have hU := goeBilinear_memLp r u u
  change cov[goeBilinear r (unitRow κ u i) (unitRow κ u k)+
    (fun g => ((ell-κ^2)*u i*u k)*goeBilinear r u u g),
    goeBilinear r (unitRow κ u l) (unitRow κ u a)+
    (fun g => ((ell-κ^2)*u l*u a)*goeBilinear r u u g);_]=_
  rw [covariance_add_left (hB i k) (hU.const_mul _) ((hB l a).add (hU.const_mul _)),
    covariance_add_right (hB i k) (hB l a) (hU.const_mul _),
    covariance_add_right (hU.const_mul _) (hB l a) (hU.const_mul _)]
  simp only [covariance_const_mul_left,covariance_const_mul_right,goe_bilinear_cov hr,
    unitRow_dot_unitRow hu,unitRow_dot hu,hu]
  have hUT (q : ι) : u⬝ᵥunitRow κ u q=κ*u q := by rw [dotProduct_comm,unitRow_dot hu]
  simp only [hUT]
  ring

end SKGap
end
end

end OAI
