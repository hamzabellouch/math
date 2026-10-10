import Mathlib
import OAI.Probability.SKGap.Gaussian.ProductGaussianDensity
import OAI.Probability.SKGap.Gaussian.ScalarMomentGram
import OAI.Probability.SKGap.Gaussian.GaussianGramMomentsJoined

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal

def scalarCurve (j t : ℝ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal (scalarFixedPoint j t) (scalarFixedPoint j t).toNNReal,inferInstance⟩

def scalarBMoment (P : ProbabilityMeasure ℝ) : ℝ := 1-scalarQMoment P

def scalarEMoment (P : ProbabilityMeasure ℝ) : ℝ := ∫ y,weightedScalarMoment 0 2 y ∂P

lemma scalarBMoment_integral (P : ProbabilityMeasure ℝ) :
    scalarBMoment P=∫ y,scalarGramVariance y ∂P := by
  unfold scalarBMoment scalarQMoment scalarGramVariance
  rw [integral_sub (integrable_const 1) integrable_tanh_sq]
  simp

lemma scalarEMoment_integral (P : ProbabilityMeasure ℝ) :
    scalarEMoment P=∫ y,spinMixed y ∂P := by
  unfold scalarEMoment
  congr 1
  funext y
  simp [weightedScalarMoment,spinMixed,scalarGramVariance]

lemma scalarBMoment_pos (P : ProbabilityMeasure ℝ) : 0 < scalarBMoment P := by
  rw [scalarBMoment_integral,integral_pos_iff_support_of_nonneg spinVariance_nonneg integrable_spinVariance]
  have he : Function.support scalarGramVariance=univ := by
    ext y
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (sub_pos.mpr (tanh_sq_lt_one y))
  rw [he,measure_univ]
  exact zero_lt_one

lemma scalarBMoment_le_one (P : ProbabilityMeasure ℝ) : scalarBMoment P ≤ 1 := by
  have h := (scalarQMoment_bounds P).1
  unfold scalarBMoment
  linarith

lemma scalarEMoment_nonneg (P : ProbabilityMeasure ℝ) : 0 ≤ scalarEMoment P := by
  rw [scalarEMoment_integral]
  exact integral_nonneg (fun y=>mul_nonneg (sq_nonneg _) (spinVariance_nonneg _))

lemma continuous_scalarBMoment : Continuous scalarBMoment := continuous_const.sub continuous_scalarQMoment
lemma continuous_scalarEMoment : Continuous scalarEMoment := continuous_weightedScalarMoment_integral 0 2

lemma continuous_scalarFixedPoint_nonneg {j : ℝ} (hj : 0 < j) (hj1 : j < 1) :
    Continuous (fun t : Ici (0:ℝ) => scalarFixedPoint j t) := by
  have hjgap : 0 < 1-j := sub_pos.mpr hj1
  have hL : LipschitzWith (⟨1/(1-j),by positivity⟩ : ℝ≥0)
      (fun t : Ici (0:ℝ) => scalarFixedPoint j t) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    change |scalarFixedPoint j t-scalarFixedPoint j u| ≤ (1/(1-j))*|((t:ℝ)-(u:ℝ))|
    exact scalarFixedPoint_lipschitz hj hj1 t.2 u.2
  exact hL.continuous

lemma continuous_scalarCurve_nonneg {j : ℝ} (hj : 0 < j) (hj1 : j < 1) :
    Continuous (fun t : Ici (0:ℝ) => scalarCurve j t) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hc := (continuous_gaussianAverage f.continuous (C := ‖f‖) (fun y=>f.norm_coe_le_norm y)).comp
    ((continuous_scalarFixedPoint_nonneg hj hj1).prodMk (continuous_scalarFixedPoint_nonneg hj hj1))
  convert hc using 1
  funext t
  exact (gaussianAverage_eq_integral f.continuous _ (scalarFixedPoint_spec hj hj1 t.2).1).symm

lemma scalarQMoment_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarQMoment (scalarCurve j t)=scalarQ j t := (scalarQ_spec hj hj1 ht).1.symm

lemma scalarM_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarM (scalarCurve j t)=scalarQ j t := by
  have hs := (scalarFixedPoint_spec hj hj1 ht).1
  have h := gaussian_nishimori (scalarFixedPoint j t).toNNReal
  simp only [Real.coe_toNNReal _ hs] at h
  exact h.trans (scalarQMoment_curve hj hj1 ht)

lemma scalarD_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarD j (scalarCurve j t,t,0)=scalarFixedPoint j t := by
  rw [scalarD,scalarM_curve hj hj1 ht]
  exact (scalarFixedPoint_spec hj hj1 ht).2.symm

lemma scalarS_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarS j (scalarCurve j t,t,0)=scalarFixedPoint j t := by
  rw [scalarS,scalarQMoment_curve hj hj1 ht]
  simpa only [zero_pow (by decide : 2 ≠ 0),add_zero,scalarQ] using (scalarFixedPoint_spec hj hj1 ht).2.symm

lemma scalarA_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 < t) :
    scalarA j (scalarCurve j t,t,0)=scalarFixedPoint j t*scalarBMoment (scalarCurve j t) := by
  let s := scalarFixedPoint j t
  have hs : 0 < s := (scalar_fixed_pos hj hj1 ht).1
  have hn : s.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hs)
  have hi : Integrable (fun y : ℝ => (y-s)*tanh y) (gaussianReal s s.toNNReal) :=
    ((IsGaussian.integrable_id (μ := gaussianReal s s.toNNReal)).sub (integrable_const s)).mul_bdd
      (c := 1) continuous_tanh.aestronglyMeasurable (ae_of_all _ (fun y=>by simpa using (abs_tanh_lt_one y).le))
  have hyt : Integrable (fun y : ℝ => y*tanh y) (gaussianReal s s.toNNReal) :=
    (IsGaussian.integrable_id (μ := gaussianReal s s.toNNReal)).mul_bdd
      (c := 1) continuous_tanh.aestronglyMeasurable (ae_of_all _ (fun y=>by simpa using (abs_tanh_lt_one y).le))
  have hibp := gaussian_integration_by_parts hn hasDerivAt_tanh integrable_tanh
    integrable_spinVariance hi
  rw [Real.coe_toNNReal _ hs.le] at hibp
  unfold scalarA
  rw [scalarD_curve hj hj1 ht.le,scalarBMoment_integral]
  change (∫ y,y*tanh y ∂gaussianReal s s.toNNReal)-s*(∫ y,tanh y ∂gaussianReal s s.toNNReal)=s*(∫ y,1-tanh y^2 ∂gaussianReal s s.toNNReal)
  rw [← integral_const_mul,← integral_sub hyt (integrable_tanh.const_mul s)]
  convert hibp using 1
  congr 1
  funext y
  ring

lemma scalarMomentGram_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 < t) :
    scalarMomentGram (scalarCurve j t) (scalarFixedPoint j t) (scalarFixedPoint j t)=
      limitingGram (scalarBMoment (scalarCurve j t)) (scalarEMoment (scalarCurve j t))
        (scalarFixedPoint j t) := by
  have hs := (scalar_fixed_pos hj hj1 ht).1
  have h := gaussian_weighted_gram_matrix (s := (scalarFixedPoint j t).toNNReal)
    (by exact_mod_cast (Real.toNNReal_pos.mpr hs))
  rw [scalarMomentGram_integral,scalarBMoment_integral,scalarEMoment_integral]
  ext i k
  simpa only [Real.coe_toNNReal _ hs.le,scalarCurve,scalarGramVector,gramCoordinates,
    scalarGramVariance,ProbabilityMeasure.coe_mk] using congrFun (congrFun h i) k
end SKGap
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKGap.GaussianDensity

lemma map_withDensity_leftInverse {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} {g : β → α} (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) (d : α → ℝ≥0∞) (hd : Measurable d) :
    (μ.withDensity d).map f=(μ.map f).withDensity (d ∘ g) := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs,
    setLIntegral_map hs (hd.comp hg) hf]
  apply lintegral_congr
  intro x
  simp only [Function.comp_apply]
  rw [hgf x]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_map_gaussian_density (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x => A*ᵥx) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal
        (|A.det⁻¹| *∏ i,gaussianPDFReal 0 1 ((A⁻¹*ᵥx) i))) := by
  have hm (B : Matrix ι ι ℝ) : Measurable (fun x => B*ᵥx) := by fun_prop
  have hleft : Function.LeftInverse (fun x => A⁻¹*ᵥx) (fun x => A*ᵥx) := by
    intro x
    change A⁻¹*ᵥ(A*ᵥx)=x
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),Matrix.one_mulVec]
  rw [pi_gaussian_density (fun _ : ι => 0) (fun _ => 1) (fun _ => one_ne_zero),
    map_withDensity_leftInverse _ (hm A) (hm A⁻¹) hleft _ (measurable_productPDF _ _)]
  have hvol : (volume : Measure (ι → ℝ)).map (fun x => A*ᵥx)=
      ENNReal.ofReal |A.det⁻¹| • volume := Real.map_matrix_volume_pi_eq_smul_volume_pi hA
  rw [hvol,withDensity_smul_measure,← withDensity_smul _ ((measurable_productPDF _ _).comp (hm A⁻¹))]
  congr 1
  ext x
  simp only [Pi.smul_apply,Function.comp_apply,smul_eq_mul,ENNReal.ofReal_mul (abs_nonneg _)]

end SKGap.GaussianDensity
end
end

end OAI
