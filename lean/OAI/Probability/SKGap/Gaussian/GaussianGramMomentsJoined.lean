import Mathlib
import OAI.Probability.SKGap.Localization.FiniteRankPositive
import OAI.Probability.SKGap.Localization.ScalarFixedPointJoined

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKGap

end SKGap

namespace SKGap

def scalarGramVariance (y : ℝ) := 1-tanh y^2

def spinMixed (y : ℝ) := tanh y^2*scalarGramVariance y

lemma spinVariance_nonneg (y : ℝ) : 0 ≤ scalarGramVariance y :=
  sub_nonneg.mpr (tanh_sq_lt_one y).le

lemma abs_spinVariance_le_one (y : ℝ) : |scalarGramVariance y| ≤ 1 := by
  rw [abs_of_nonneg (spinVariance_nonneg y)]
  unfold scalarGramVariance
  nlinarith [sq_nonneg (tanh y)]

lemma abs_spinMixed_le_one (y : ℝ) : |spinMixed y| ≤ 1 := by
  unfold spinMixed
  rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ 1*1 := mul_le_mul (tanh_sq_lt_one y).le (abs_spinVariance_le_one y) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma integrable_spinVariance {μ : Measure ℝ} [IsFiniteMeasure μ] : Integrable scalarGramVariance μ :=
  Integrable.of_bound (by unfold scalarGramVariance; fun_prop) 1
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using abs_spinVariance_le_one y))

lemma integrable_spinMixed {μ : Measure ℝ} [IsFiniteMeasure μ] : Integrable spinMixed μ :=
  Integrable.of_bound (by unfold spinMixed scalarGramVariance; fun_prop) 1
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using abs_spinMixed_le_one y))

lemma gaussian_nishimori_variance (s : ℝ≥0) :
    (∫ y, oddVariance y ∂gaussianReal s s) = ∫ y, spinMixed y ∂gaussianReal s s := by
  by_cases hs : s = 0
  · subst s; simp [oddVariance,spinMixed,scalarGramVariance]
  have hi := (integrable_gaussian_iff hs).mp
    (integrable_oddVariance.sub (integrable_spinMixed (μ := gaussianReal s s)))
  let f : ℝ → ℝ := fun y => gaussianPDFReal s s y*(oddVariance y-spinMixed y)
  have hf : Integrable f := hi
  have hid (y : ℝ) : f y+f (-y) = 0 := by
    have hh := gaussianPDFReal_diagonal_symmetry hs y
    dsimp [f,oddVariance,spinMixed,scalarGramVariance]
    rw [tanh_neg,neg_sq]
    nlinarith [congrArg (fun x => tanh y*(1-tanh y^2)*x) hh]
  have hz : (∫ y, f y)+(∫ y, f (-y)) = 0 := by
    rw [← integral_add hf hf.comp_neg]
    simp only [hid,integral_zero]
  rw [integral_neg_eq_self] at hz
  have hsub : ∫ y, oddVariance y-spinMixed y ∂gaussianReal s s = 0 := by
    rw [integral_gaussianReal_eq_integral_smul hs]
    change (∫ y, f y) = 0
    linarith
  rw [integral_sub integrable_oddVariance integrable_spinMixed] at hsub
  exact sub_eq_zero.mp hsub

lemma hasDerivAt_spinVariance (y : ℝ) : HasDerivAt scalarGramVariance (-2*oddVariance y) y := by
  convert! (hasDerivAt_const y (1:ℝ)).sub ((hasDerivAt_tanh y).pow 2) using 1
  simp only [oddVariance]; norm_num; ring

lemma hasDerivAt_oddVariance (y : ℝ) :
    HasDerivAt oddVariance (scalarGramVariance y-3*spinMixed y) y := by
  convert! (hasDerivAt_tanh y).mul (hasDerivAt_spinVariance y) using 1
  simp only [spinMixed,scalarGramVariance,oddVariance]; ring

lemma integrable_center_spinVariance (d : ℝ) (s : ℝ≥0) :
    Integrable (fun y => (y-d)*scalarGramVariance y) (gaussianReal d s) := by
  have h := ((IsGaussian.integrable_id (μ := gaussianReal d s)).sub (integrable_const d)).bdd_mul (f := scalarGramVariance)
    (by unfold scalarGramVariance; fun_prop) (c := 1)
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using abs_spinVariance_le_one y))
  simpa only [mul_comm,Pi.sub_apply,id_eq] using h

lemma integrable_center_oddVariance (d : ℝ) (s : ℝ≥0) :
    Integrable (fun y => (y-d)*oddVariance y) (gaussianReal d s) := by
  have h := ((IsGaussian.integrable_id (μ := gaussianReal d s)).sub (integrable_const d)).bdd_mul (f := oddVariance)
    (by unfold oddVariance; fun_prop) (c := 1)
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using abs_oddVariance_le_one y))
  simpa only [mul_comm,Pi.sub_apply,id_eq] using h

lemma integrable_center_sq_spinVariance (d : ℝ) (s : ℝ≥0) :
    Integrable (fun y => (y-d)^2*scalarGramVariance y) (gaussianReal d s) := by
  have hmem : MemLp (fun y : ℝ => y-d) 2 (gaussianReal d s) :=
    (IsGaussian.memLp_id (gaussianReal d s) 2 (by norm_num)).sub (memLp_const d)
  have h := hmem.integrable_sq.bdd_mul (f := scalarGramVariance)
    (by unfold scalarGramVariance; fun_prop) (c := 1)
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using abs_spinVariance_le_one y))
  simpa only [mul_comm,Pi.sub_apply,id_eq] using h

theorem gaussian_weighted_gram_moments {s : ℝ≥0} (hs : 0 < s) :
    (∫ y, (y-(s:ℝ))*scalarGramVariance y ∂gaussianReal s s) =
      -2*(s:ℝ)*(∫ y, spinMixed y ∂gaussianReal s s) ∧
    (∫ y, (y-(s:ℝ))*oddVariance y ∂gaussianReal s s) =
      (s:ℝ)*((∫ y, scalarGramVariance y ∂gaussianReal s s)-3*(∫ y, spinMixed y ∂gaussianReal s s)) ∧
    (∫ y, (y-(s:ℝ))^2*scalarGramVariance y ∂gaussianReal s s) =
      (s:ℝ)*(∫ y, scalarGramVariance y ∂gaussianReal s s)+
      (s:ℝ)^2*(-2*(∫ y, scalarGramVariance y ∂gaussianReal s s)+6*(∫ y, spinMixed y ∂gaussianReal s s)) := by
  have h1 := gaussian_integration_by_parts hs.ne' hasDerivAt_spinVariance
    integrable_spinVariance (integrable_oddVariance.const_mul (-2))
    (integrable_center_spinVariance s s)
  rw [integral_const_mul,gaussian_nishimori_variance] at h1
  have h2 := gaussian_integration_by_parts hs.ne' hasDerivAt_oddVariance
    integrable_oddVariance (integrable_spinVariance.sub (integrable_spinMixed.const_mul 3))
    (integrable_center_oddVariance s s)
  rw [integral_sub integrable_spinVariance (integrable_spinMixed.const_mul 3),integral_const_mul] at h2
  have hder (y : ℝ) : HasDerivAt (fun y => (y-(s:ℝ))*scalarGramVariance y)
      (scalarGramVariance y-2*((y-(s:ℝ))*oddVariance y)) y := by
    convert! ((hasDerivAt_id y).sub_const (s:ℝ)).mul (hasDerivAt_spinVariance y) using 1
    simp only [id_eq,one_mul]; ring
  have h3 := gaussian_integration_by_parts hs.ne' hder (integrable_center_spinVariance s s)
    (integrable_spinVariance.sub ((integrable_center_oddVariance s s).const_mul 2))
    ((integrable_center_sq_spinVariance s s).congr (ae_of_all _ (fun y => by ring)))
  have h3' : (∫ y, (y-(s:ℝ))^2*scalarGramVariance y ∂gaussianReal s s) =
      (s:ℝ)*((∫ y, scalarGramVariance y ∂gaussianReal s s)-2*(∫ y, (y-(s:ℝ))*oddVariance y ∂gaussianReal s s)) := by
    convert h3 using 1
    · congr 1; funext y; ring
    · rw [integral_sub integrable_spinVariance ((integrable_center_oddVariance s s).const_mul 2),integral_const_mul]
  refine ⟨?_,h2,?_⟩
  · linarith [h1]
  · rw [h3',h2]; ring

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

def scalarGramVector (s y : ℝ) : Fin 3 → ℝ := ![1,tanh y,(y-s)/s]

theorem gaussian_weighted_gram_matrix {s : ℝ≥0} (hs : 0 < s) :
    (fun i k : Fin 3 => ∫ y, scalarGramVariance y*scalarGramVector s y i*scalarGramVector s y k
      ∂gaussianReal s s)=
      limitingGram (∫ y,scalarGramVariance y ∂gaussianReal s s)
        (∫ y,spinMixed y ∂gaussianReal s s) s := by
  have hsR : (s:ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  obtain ⟨h1,h2,h3⟩ := gaussian_weighted_gram_moments hs
  have h01 : (∫ y,scalarGramVariance y*tanh y ∂gaussianReal s s)=∫ y,spinMixed y ∂gaussianReal s s := by
    convert gaussian_nishimori_variance s using 1
    congr 1; funext y; unfold oddVariance scalarGramVariance; ring
  have h02 : (∫ y,scalarGramVariance y*((y-(s:ℝ))/(s:ℝ)) ∂gaussianReal s s)=
      -2*(∫ y,spinMixed y ∂gaussianReal s s) := by
    calc
      _ = (∫ y,(y-(s:ℝ))*scalarGramVariance y ∂gaussianReal s s)/(s:ℝ) := by
        rw [← integral_div]; congr 1; funext y; ring
      _ = _ := by rw [h1]; field_simp
  have h11 : (∫ y,scalarGramVariance y*tanh y*tanh y ∂gaussianReal s s)=
      ∫ y,spinMixed y ∂gaussianReal s s := by
    congr 1; funext y; unfold spinMixed; ring
  have h12 : (∫ y,scalarGramVariance y*tanh y*((y-(s:ℝ))/(s:ℝ)) ∂gaussianReal s s)=
      (∫ y,scalarGramVariance y ∂gaussianReal s s)-3*(∫ y,spinMixed y ∂gaussianReal s s) := by
    calc
      _ = (∫ y,(y-(s:ℝ))*oddVariance y ∂gaussianReal s s)/(s:ℝ) := by
        rw [← integral_div]; congr 1; funext y; unfold oddVariance scalarGramVariance; ring
      _ = _ := by rw [h2]; field_simp
  have h22 : (∫ y,scalarGramVariance y*((y-(s:ℝ))/(s:ℝ))*((y-(s:ℝ))/(s:ℝ)) ∂gaussianReal s s)=
      (∫ y,scalarGramVariance y ∂gaussianReal s s)/(s:ℝ)-
        2*(∫ y,scalarGramVariance y ∂gaussianReal s s)+6*(∫ y,spinMixed y ∂gaussianReal s s) := by
    calc
      _ = (∫ y,(y-(s:ℝ))^2*scalarGramVariance y ∂gaussianReal s s)/(s:ℝ)^2 := by
        rw [← integral_div]; congr 1; funext y; ring
      _ = _ := by rw [h3]; field_simp; ring
  have hsym (i k : Fin 3) :
      (∫ y,scalarGramVariance y*scalarGramVector s y i*scalarGramVector s y k ∂gaussianReal s s)=
        ∫ y,scalarGramVariance y*scalarGramVector s y k*scalarGramVector s y i ∂gaussianReal s s := by
    congr 1; funext y; ring
  ext i k
  fin_cases i <;> fin_cases k
  · simp [scalarGramVector,limitingGram]
  · simpa [scalarGramVector,limitingGram] using h01
  · simpa [scalarGramVector,limitingGram] using h02
  · simpa [scalarGramVector,limitingGram] using (hsym 1 0).trans (by simpa [scalarGramVector] using h01)
  · simpa [scalarGramVector,limitingGram] using h11
  · simpa [scalarGramVector,limitingGram] using h12
  · simpa [scalarGramVector,limitingGram] using (hsym 2 0).trans (by simpa [scalarGramVector] using h02)
  · simpa [scalarGramVector,limitingGram] using (hsym 2 1).trans (by simpa [scalarGramVector] using h12)
  · simpa [scalarGramVector,limitingGram] using h22

end SKGap
end
end

end OAI
