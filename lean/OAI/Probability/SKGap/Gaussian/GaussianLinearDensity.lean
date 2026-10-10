import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianRegression
import OAI.Probability.SKGap.Localization.EqualityCurve
import OAI.Probability.SKGap.Localization.RankCovariance

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → ι → ℝ}

theorem gaussian_density_of_matrix (hX : HasGaussianLaw X P) (A : Matrix ι ι ℝ) (hA : A.det ≠ 0)
    (hm : ∀ i,(∫ w,X w i ∂P)=0)
    (hc : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=(A*Aᵀ) i k) :
    P.map X=(volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal
      (|A.det⁻¹| *∏ i,gaussianPDFReal 0 1 ((A⁻¹*ᵥx) i))) := by
  have hl : P.map X=(gaussianCoordinates ι).map (fun x => A*ᵥx) := by
    apply GaussianRegression.law_eq_of_mean_covariance hX (matrix_sample_gaussian A)
    · intro i
      rw [hm]
      exact (linear_gaussian_mean (A i)).symm
    · intro i k
      rw [hc,matrix_sample_covariance]
  rw [hl]
  exact matrix_map_gaussian_density A hA

lemma gaussian_rankOne_density (hX : HasGaussianLaw X P) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) (hm : ∀ i,(∫ w,X w i ∂P)=0)
    (hc : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=
      rankOneTransform (a^2) (b^2) u i k) :
    P.map X=(volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal
      ((a^(Fintype.card ι)*(b/a))⁻¹*∏ i,gaussianPDFReal 0 1
        ((rankOneTransform a⁻¹ b⁻¹ u*ᵥx) i))) := by
  have hd : 0 < (rankOneTransform a b u).det := by
    rw [rankOneTransform_det ha.ne' b hu]
    positivity
  have hc' : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=
      (rankOneTransform a b u*(rankOneTransform a b u)ᵀ) i k := by
    intro i k
    rw [hc,rankOneTransform_transpose,rankOneTransform_mul hu]
    simp only [← pow_two]
  rw [gaussian_density_of_matrix hX _ hd.ne' hm hc',
    rankOneTransform_inv ha.ne' hb.ne' hu,abs_of_pos (inv_pos.mpr hd),rankOneTransform_det ha.ne' b hu]

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def radialDensity (a : ℝ) (x : ι → ℝ) : ℝ :=
  ((sqrt (2*Real.pi)*a)⁻¹)^(Fintype.card ι)*exp (-(x⬝ᵥx)/(2*a^2))

omit [DecidableEq ι] in
lemma product_gaussianPDF_formula (v : ℝ≥0) (x : ι → ℝ) :
    (∏ i,gaussianPDFReal 0 v (x i))=(sqrt (2*Real.pi*v))⁻¹^(Fintype.card ι)*
      exp (-(x⬝ᵥx)/(2*v)) := by
  simp only [gaussianPDFReal,sub_zero,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,← exp_sum,← Finset.sum_div,← Finset.sum_neg_distrib,dotProduct,← pow_two]

omit [DecidableEq ι] in
lemma product_gaussianPDF_radial {a : ℝ} (ha : 0 ≤ a) (x : ι → ℝ) :
    (∏ i,gaussianPDFReal 0 (NNReal.mk (a^2) (sq_nonneg a)) (x i))=radialDensity a x := by
  rw [product_gaussianPDF_formula]
  simp only [NNReal.coe_mk,radialDensity,sqrt_mul (by positivity : 0 ≤ 2*Real.pi),sqrt_sq ha]

lemma rankOne_density_radial {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) (x : ι → ℝ) :
    (a^(Fintype.card ι)*(b/a))⁻¹*(∏ i,gaussianPDFReal 0 1
      ((rankOneTransform a⁻¹ b⁻¹ u*ᵥx) i)) =
    (a/b)*radialDensity a x*exp ((b^2-a^2)/(2*a^2*b^2)*(u⬝ᵥx)^2) := by
  rw [product_gaussianPDF_formula,rankOneTransform_norm_sq hu]
  simp only [NNReal.coe_one,mul_one]
  have he : -(a⁻¹^2*(x⬝ᵥx)+(b⁻¹^2-a⁻¹^2)*(u⬝ᵥx)^2)/2 =
      -(x⬝ᵥx)/(2*a^2)+(b^2-a^2)/(2*a^2*b^2)*(u⬝ᵥx)^2 := by
    field_simp
    ring
  rw [he,exp_add]
  unfold radialDensity
  have hc : (a^(Fintype.card ι)*(b/a))⁻¹*(sqrt (2*Real.pi))⁻¹^(Fintype.card ι)=
      (a/b)*((sqrt (2*Real.pi)*a)⁻¹)^(Fintype.card ι) := by
    simp only [_root_.mul_inv_rev,mul_pow,inv_pow,inv_inv,div_eq_mul_inv]
    ring
  rw [← mul_assoc,← mul_assoc,hc]
  ring

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → ι → ℝ}

def rankOneDensity (s r : ℝ) (m x : ι → ℝ) : ℝ :=
  sqrt (s/(s+r*(m⬝ᵥm)))*radialDensity (sqrt s) x*
    exp (r/(2*s*(s+r*(m⬝ᵥm)))*(m⬝ᵥx)^2)

omit [Fintype ι] in
lemma rankOne_scaled_covariance (s r c : ℝ) (u : ι → ℝ) :
    rankOneCovariance s r (c • u)=rankOneTransform s (s+r*c^2) u := by
  ext i k
  simp only [rankOneCovariance,rankOneTransform,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.vecMulVec_apply,Pi.smul_apply]
  ring

lemma scaled_unit_exists [Nonempty ι] (m : ι → ℝ) :
    ∃ (c : ℝ) (u : ι → ℝ), 0 ≤ c ∧ u⬝ᵥu=1 ∧ m=c • u := by
  by_cases hm : m=0
  · let i : ι := Classical.choice inferInstance
    refine ⟨0,Pi.single i 1,le_rfl,?_,by simp [hm]⟩
    simp [dotProduct,Pi.single_apply]
  · have hq : 0 < m⬝ᵥm := lt_of_le_of_ne
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg (m i)))
      (Ne.symm (mt dotProduct_self_eq_zero.mp hm))
    have hc : 0 < sqrt (m⬝ᵥm) := sqrt_pos.mpr hq
    refine ⟨sqrt (m⬝ᵥm),(sqrt (m⬝ᵥm))⁻¹ • m,hc.le,?_,?_⟩
    · simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul]
      have hh := sq_sqrt hq.le
      field_simp
      nlinarith
    · simp [smul_smul,hc.ne']

theorem gaussian_rankOne_covariance_density [Nonempty ι]
    (hX : HasGaussianLaw X P) {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r)
    (m : ι → ℝ) (hm : ∀ i,(∫ w,X w i ∂P)=0)
    (hc : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=rankOneCovariance s r m i k) :
    P.map X=(volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (rankOneDensity s r m x)) := by
  obtain ⟨c,u,hcpos,hu,rfl⟩ := scaled_unit_exists m
  have hS : 0 < s+r*c^2 := add_pos_of_pos_of_nonneg hs (mul_nonneg hr (sq_nonneg c))
  have ha : 0 < sqrt s := sqrt_pos.mpr hs
  have hb : 0 < sqrt (s+r*c^2) := sqrt_pos.mpr hS
  have hc' : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=
      rankOneTransform ((sqrt s)^2) ((sqrt (s+r*c^2))^2) u i k := by
    intro i k
    rw [sq_sqrt hs.le,sq_sqrt hS.le,hc,rankOne_scaled_covariance]
  rw [gaussian_rankOne_density hX ha hb hu hm hc']
  congr 1
  ext x
  rw [rankOne_density_radial ha.ne' hb.ne' hu x]
  simp only [rankOneDensity,smul_dotProduct,dotProduct_smul,smul_eq_mul,hu,mul_one,
    sq_sqrt hs.le,sq_sqrt hS.le]
  have hq : c*c=c^2 := by ring
  rw [hq]
  have hpref : sqrt s/sqrt (s+r*c^2)=sqrt (s/(s+r*c^2)) := (sqrt_div hs.le _).symm
  rw [hpref]
  congr 2
  congr 1
  field_simp
  ring

end SKGap.GaussianDensity
end
end

end OAI
