import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianVectorMoments
import OAI.Probability.SKGap.Localization.LocalWhitening

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal

lemma matrix_fourth_sum_integrable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) :
    Integrable (fun g => ∑ i,((A*ᵥg) i)^4) (gaussianCoordinates κ) := by
  apply integrable_finsetSum
  intro i _
  exact linear_gaussian_fourth_integrable (A i)

lemma matrix_fourth_sum_mean {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) :
    (∫ g,∑ i,((A*ᵥg) i)^4 ∂gaussianCoordinates κ)=3*∑ i,(∑ k,A i k^2)^2 := by
  simp only [Matrix.mulVec,dotProduct]
  rw [integral_finsetSum _ (fun i _ => linear_gaussian_fourth_integrable (A i)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact linear_gaussian_fourth (A i)

lemma matrix_fourth_sum_bound {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ i,∑ k,A i k^2 ≤ c) :
    (∫ g,∑ i,((A*ᵥg) i)^4 ∂gaussianCoordinates (Fin m)) ≤ 3*(n:ℝ)*c^2 := by
  rw [matrix_fourth_sum_mean]
  have hs : (∑ i : Fin n,(∑ k,A i k^2)^2) ≤ ∑ _i : Fin n,c^2 := by
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq₀ (Finset.sum_nonneg (fun k _ => sq_nonneg _)) hc).mpr (hb i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  nlinarith

lemma matrix_norm_fourth_integrable {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    Integrable (fun g => vectorNorm (A*ᵥg)^4) (gaussianCoordinates (Fin m)) := by
  apply ((matrix_fourth_sum_integrable A).const_mul (n:ℝ)).mono' ?_ ?_
  · have he : (fun g => vectorNorm (A*ᵥg)^4)=fun g => (∑ i,((A*ᵥg) i)^2)^2 := by
      funext g
      rw [show vectorNorm (A*ᵥg)^4=(vectorNorm (A*ᵥg)^2)^2 by ring,vectorNorm_sq]
      rfl
    rw [he]
    fun_prop
  · filter_upwards [] with g
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact vectorNorm_fourth_le (A*ᵥg)

lemma matrix_norm_fourth_bound {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ i,∑ k,A i k^2 ≤ c) :
    (∫ g,vectorNorm (A*ᵥg)^4 ∂gaussianCoordinates (Fin m)) ≤ 3*(n:ℝ)^2*c^2 := by
  calc
    _ ≤ ∫ g,(n:ℝ)*(∑ i,((A*ᵥg) i)^4) ∂gaussianCoordinates (Fin m) :=
      integral_mono (matrix_norm_fourth_integrable A)
        ((matrix_fourth_sum_integrable A).const_mul _) (fun g => vectorNorm_fourth_le _)
    _ = (n:ℝ)*(∫ g,∑ i,((A*ᵥg) i)^4 ∂gaussianCoordinates (Fin m)) := integral_const_mul _ _
    _ ≤ (n:ℝ)*(3*(n:ℝ)*c^2) := mul_le_mul_of_nonneg_left (matrix_fourth_sum_bound A hc hb) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem localGaussian_fourth_moments {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U.IsHermitian) {γ σ : ℝ} (hγ : 0 < γ)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ) :
    (∫ g,∑ i,((σ • U)*ᵥg) i^4 ∂gaussianCoordinates (Fin n)) ≤ 3*(n:ℝ)*σ^4/γ^2 ∧
    (∫ g,vectorNorm ((σ • U)*ᵥg)^4 ∂gaussianCoordinates (Fin n)) ≤ 3*(n:ℝ)^2*σ^4/γ^2 := by
  have hb (i : Fin n) : ∑ k,(σ • U) i k^2 ≤ σ^2/γ := by
    have hh := symmetric_row_sq_bound hU (inv_nonneg.mpr (sqrt_nonneg γ))
      (fun g => by simpa only [div_eq_mul_inv,mul_comm] using hbound g) i
    rw [inv_pow,Real.sq_sqrt hγ.le] at hh
    simp only [Matrix.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg σ)).trans_eq (by ring)
  have h1 := matrix_fourth_sum_bound (σ • U) (div_nonneg (sq_nonneg σ) hγ.le) hb
  have h2 := matrix_norm_fourth_bound (σ • U) (div_nonneg (sq_nonneg σ) hγ.le) hb
  constructor
  · convert h1 using 1; ring
  · convert h2 using 1; ring

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma gaussian_vectorSqNorm_integrable (n : ℕ) :
    Integrable (vectorSqNorm (n := n)) (gaussianCoordinates (Fin n)) := by
  have hh := (gaussianQuadratic_memLp (fun _ : Fin n => (1:ℝ))).integrable (by norm_num)
  change Integrable (fun g : Field n => ∑ i,1*g i^2) (gaussianCoordinates (Fin n)) at hh
  change Integrable (fun g : Field n => ∑ i,g i^2) (gaussianCoordinates (Fin n))
  simpa only [one_mul] using hh

lemma gaussian_vectorSqNorm_mean (n : ℕ) :
    (∫ g,vectorSqNorm g ∂gaussianCoordinates (Fin n))=(n:ℝ) := by
  simpa only [vectorSqNorm,gaussianQuadratic,one_mul,gaussianCoordinates,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
    gaussianQuadratic_mean (fun _ : Fin n => (1:ℝ))

def localGaussianBall (n : ℕ) : Set (Field n) := {g | vectorSqNorm g ≤ 4*(n:ℝ)}

lemma localGaussianBall_measurable (n : ℕ) : MeasurableSet (localGaussianBall n) := by
  unfold localGaussianBall vectorSqNorm
  exact measurableSet_le (by fun_prop) measurable_const

lemma localGaussianBall_norm {n : ℕ} {g : Field n} (hg : g ∈ localGaussianBall n) :
    vectorNorm g ≤ 2*sqrt (n:ℝ) := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (by positivity)).mp
  rw [vectorNorm_sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  simpa only [localGaussianBall,Set.mem_ofPred_eq,show (2:ℝ)^2=4 by norm_num] using hg

theorem localGaussianBall_probability {n : ℕ} (hn : 0 < n) :
    3/4 ≤ (gaussianCoordinates (Fin n)).real (localGaussianBall n) := by
  let μ := gaussianCoordinates (Fin n)
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hh := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (ae_of_all _ (fun g => vectorSqNorm_nonneg g))
    (gaussian_vectorSqNorm_integrable n) (4*(n:ℝ))
  rw [gaussian_vectorSqNorm_mean] at hh
  have hsub : (localGaussianBall n)ᶜ ⊆ {g | 4*(n:ℝ) ≤ vectorSqNorm g} := by
    intro g hg
    change ¬ vectorSqNorm g ≤ 4*(n:ℝ) at hg
    exact (lt_of_not_ge hg).le
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have hc := probReal_compl_eq_one_sub (μ := μ) (localGaussianBall_measurable n)
  rw [hc] at hmono
  nlinarith

lemma localGaussianBall_ne_zero {n : ℕ} (hn : 0 < n) :
    gaussianCoordinates (Fin n) (localGaussianBall n) ≠ 0 := by
  intro he
  have hh := localGaussianBall_probability hn
  simp only [measureReal_def,he,ENNReal.toReal_zero] at hh
  norm_num at hh

lemma integrable_cond_of_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {s : Set Ω} {f : Ω → E}
    (hs : μ s ≠ 0) (hf : Integrable f μ) : Integrable f (cond μ s) := by
  exact hf.restrict.smul_measure (ENNReal.inv_ne_top.mpr hs)

lemma integral_cond_nonneg_le_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω} {f : Ω → ℝ}
    (hp : 1/2 ≤ μ.real s)
    (hf : Integrable f μ) (hn : 0 ≤ᵐ[μ] f) :
    (∫ x,f x ∂cond μ s) ≤ 2*∫ x,f x ∂μ := by
  have hps : 0 < μ.real s := by linarith
  have his : 0 ≤ ∫ x in s,f x ∂μ := integral_nonneg_of_ae (ae_restrict_of_ae hn)
  have hsle : (∫ x in s,f x ∂μ) ≤ ∫ x,f x ∂μ :=
    integral_mono_measure μ.restrict_le_self hn hf
  have hinv : (μ.real s)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hps).mpr (by linarith)
  rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv]
  change (μ.real s)⁻¹*(∫ x in s,f x ∂μ) ≤ _
  exact (mul_le_mul_of_nonneg_right hinv his).trans (mul_le_mul_of_nonneg_left hsle (by norm_num))

end SKGap
end
end

end OAI
