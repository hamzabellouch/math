import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianCoordinates

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKGap.GaussianRegression

theorem law_eq_of_mean_covariance {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {P' : Measure Ω'} {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P')
    (hm : ∀ i, (∫ w, X w i ∂P) = ∫ w, Y w i ∂P')
    (hc : ∀ i k, cov[fun w => X w i, fun w => X w k; P] =
      cov[fun w => Y w i, fun w => Y w k; P']) :
    P.map X = P'.map Y := by
  classical
  have := hX.isProbabilityMeasure
  have := hY.isProbabilityMeasure
  apply Measure.ext_of_charFunDual
  ext L
  rw [hX.charFunDual_map_eq,hY.charFunDual_map_eq]
  let c : ι → ℝ := fun i => L (fun k => if i=k then 1 else 0)
  have hL (x : ι → ℝ) : L x = ∑ i, x i * c i := by
    simpa only [c, smul_eq_mul, ContinuousLinearMap.coe_coe] using L.toLinearMap.pi_apply_eq_sum_univ x
  have hLX : L ∘ X = fun w => ∑ i, X w i*c i := funext (fun w => hL (X w))
  have hLY : L ∘ Y = fun w => ∑ i, Y w i*c i := funext (fun w => hL (Y w))
  have hiX (i : ι) := (hX.eval i).memLp_two
  have hiY (i : ι) := (hY.eval i).memLp_two
  have hem : (∫ w, (L ∘ X) w ∂P) = ∫ w, (L ∘ Y) w ∂P' := by
    rw [hLX,hLY]
    rw [integral_finsetSum _ (fun i _ => ((hX.eval i).integrable.mul_const _)),
      integral_finsetSum _ (fun i _ => ((hY.eval i).integrable.mul_const _))]
    simp only [integral_mul_const,hm]
  have hev : Var[L ∘ X; P] = Var[L ∘ Y; P'] := by
    rw [← covariance_self (hX.map L).aemeasurable,
      ← covariance_self (hY.map L).aemeasurable]
    rw [hLX,hLY]
    rw [covariance_fun_sum_fun_sum (fun i => (hiX i).mul_const _) (fun i => (hiX i).mul_const _),
      covariance_fun_sum_fun_sum (fun i => (hiY i).mul_const _) (fun i => (hiY i).mul_const _)]
    simp only [covariance_mul_const_left,covariance_mul_const_right,hc]
  rw [hev,hem]

def matrixCLM {ι κ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) :
    (κ → ℝ) →L[ℝ] (ι → ℝ) := A.mulVecLin.toContinuousLinearMap

@[simp] lemma matrixCLM_apply {ι κ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) (x : κ → ℝ) :
    matrixCLM A x = A *ᵥ x := rfl

theorem residual_independent {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P) (K : Matrix ι κ ℝ)
    (hcov : ∀ i k, cov[fun w => X w i, fun w => Y w k; P] =
      ∑ l, K i l * cov[fun w => Y w l,fun w => Y w k; P]) :
    IndepFun (fun w => X w-K*ᵥ Y w) Y P := by
  have := hXY.isProbabilityMeasure
  have hR : HasGaussianLaw (fun w => (X w-K*ᵥ Y w,Y w)) P := by
    exact hXY.map_fun (((ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ))-
      (matrixCLM K).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ))).prod
      (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ)))
  apply hR.indepFun_of_covariance_eval
  intro i k
  change cov[fun w => X w i-∑ l, K i l*Y w l,fun w => Y w k; P]=0
  have hK : MemLp (fun w => ∑ l, K i l*Y w l) 2 P :=
    ((hXY.snd.map (matrixCLM K)).eval i).memLp_two
  rw [covariance_fun_sub_left (hXY.fst.eval i).memLp_two hK (hXY.snd.eval k).memLp_two]
  rw [covariance_fun_sum_left (fun l => (hXY.snd.eval l).memLp_two.const_mul _)
    (hXY.snd.eval k).memLp_two]
  simp only [covariance_const_mul_left,hcov,sub_self]

end SKGap.GaussianRegression
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal

lemma coordinate_hasLaw {κ : Type*} [Fintype κ] (i : κ) :
    HasLaw (fun g : κ → ℝ => g i) (gaussianReal 0 1) (gaussianCoordinates κ) :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) i).map_eq⟩

lemma coordinates_gaussian {κ : Type*} [Fintype κ] :
    HasGaussianLaw (fun g : κ → ℝ => g) (gaussianCoordinates κ) :=
  (iIndepFun_pi (fun _ : κ => aemeasurable_id)).hasGaussianLaw
    (fun i => (coordinate_hasLaw i).hasGaussianLaw)

lemma coordinate_covariance {κ : Type*} [Fintype κ] [DecidableEq κ] (i k : κ) :
    cov[fun g : κ → ℝ => g i,fun g : κ → ℝ => g k;gaussianCoordinates κ] =
      if i=k then 1 else 0 := by
  by_cases h : i=k
  · subst k
    rw [ite_eq_left rfl,covariance_self (measurable_pi_apply i).aemeasurable,
      (coordinate_hasLaw i).variance_eq]
    simp
  · rw [ite_eq_right h]
    exact ((iIndepFun_pi (fun _ : κ => aemeasurable_id)).indepFun h).covariance_eq_zero
      (coordinate_hasLaw i).hasGaussianLaw.memLp_two (coordinate_hasLaw k).hasGaussianLaw.memLp_two

lemma linear_gaussian_mean {κ : Type*} [Fintype κ] (a : κ → ℝ) :
    (∫ g, ∑ i, a i*g i ∂gaussianCoordinates κ) = 0 := by
  rw [integral_finsetSum _ (fun i _ => (coordinate_hasLaw i).hasGaussianLaw.integrable.const_mul _)]
  simp [integral_const_mul,(coordinate_hasLaw _).integral_eq]

lemma linear_gaussian_covariance {κ : Type*} [Fintype κ] [DecidableEq κ] (a b : κ → ℝ) :
    cov[fun g => ∑ i, a i*g i,fun g => ∑ i, b i*g i;gaussianCoordinates κ] =
      ∑ i, a i*b i := by
  rw [covariance_fun_sum_fun_sum
    (fun i => (coordinate_hasLaw i).hasGaussianLaw.memLp_two.const_mul _)
    (fun i => (coordinate_hasLaw i).hasGaussianLaw.memLp_two.const_mul _)]
  simp only [covariance_const_mul_left,covariance_const_mul_right,coordinate_covariance]
  simp [mul_comm]

lemma matrix_sample_gaussian {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) :
    HasGaussianLaw (fun g => A*ᵥg) (gaussianCoordinates κ) :=
  coordinates_gaussian.map_fun (GaussianRegression.matrixCLM A)

lemma matrix_sample_covariance {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (i k : ι) :
    cov[fun g => (A*ᵥg) i,fun g => (A*ᵥg) k;gaussianCoordinates κ] = (A*Aᵀ) i k :=
  linear_gaussian_covariance (A i) (A k)

end SKGap
end
end

end OAI
