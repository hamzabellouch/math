import OAI.Probability.SLE.Angle.AngleSpectralPairing
import OAI.Probability.SLE.Angle.AngleSpectralKernel

namespace OAI

/-! The positive spectral kernel has exactly the eigenfunction moments
required of the centered angular transition. -/
noncomputable section
open Polynomial Set _root_.MeasureTheory _root_.OAI.MeasureTheory

namespace SLEExactGauge

def angleSpectralTerm (κ u : ℝ) (n : ℕ) (θ φ : ℝ) : ℝ :=
  Real.exp (-u*anglePolynomialEigenvalue κ n)*
    angleSpectralFactor κ n (Real.cos θ) (Real.cos φ)

lemma angleSpectralTerm_measurable (κ u : ℝ) (n : ℕ) (θ : ℝ) :
    Measurable (angleSpectralTerm κ u n θ) := by
  unfold angleSpectralTerm angleSpectralFactor
  fun_prop

lemma angleSpectralTerm_zero {κ : ℝ} (hκ : 0<κ) (u θ φ : ℝ) :
    angleSpectralTerm κ u 0 θ φ=1 := by
  simp [angleSpectralTerm,anglePolynomialEigenvalue,angleSpectralFactor_zero hκ]

lemma angleSpectralTerm_bound_all {κ u : ℝ} (hκ : 0<κ)
    (hu : angleSpectralMixingTime κ≤u) (n : ℕ) (θ φ : ℝ) :
    ‖angleSpectralTerm κ u n θ φ‖≤(1/3:ℝ)^n := by
  cases n with
  | zero => simp [angleSpectralTerm_zero hκ]
  | succ n =>
    exact angleSpectralTerm_bound hκ hu (by omega)
      (Real.abs_cos_le_one θ) (Real.abs_cos_le_one φ)

lemma angleSpectralKernel_eq_tsum {κ u : ℝ} (hκ : 0<κ)
    (hu : angleSpectralMixingTime κ≤u) (θ φ : ℝ) :
    angleSpectralKernel κ u θ φ=∑' n : ℕ, angleSpectralTerm κ u n θ φ := by
  have hs : Summable (fun n : ℕ => angleSpectralTerm κ u n θ φ) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/3)
      (by norm_num : (1/3:ℝ)<1)).of_norm_bounded
        (fun n => angleSpectralTerm_bound_all hκ hu n θ φ)
  calc
    _ = angleSpectralTerm κ u 0 θ φ+∑' n : ℕ, angleSpectralTerm κ u (n+1) θ φ := by
      rw [angleSpectralTerm_zero hκ]
      rfl
    _ = _ := hs.tsum_eq_zero_add.symm

lemma angleSpectralKernel_measurable {κ u : ℝ} (hκ : 0<κ)
    (hu : angleSpectralMixingTime κ≤u) (θ : ℝ) :
    Measurable (angleSpectralKernel κ u θ) := by
  have he : angleSpectralKernel κ u θ=(fun φ => ∑' n : ℕ, angleSpectralTerm κ u n θ φ) :=
    funext (angleSpectralKernel_eq_tsum hκ hu θ)
  rw [he]
  exact Measurable.tsum (fun n => angleSpectralTerm_measurable κ u n θ)

lemma angleSpectralTerm_pairing {κ : ℝ} (hκ : 0<κ) (u θ : ℝ) (n m : ℕ) :
    (∫ φ, angleSpectralTerm κ u n θ φ*anglePolynomialTest (angleEigenPolynomial κ m) φ
      ∂Target.angleLaw κ)=
      if n=m then Real.exp (-u*anglePolynomialEigenvalue κ m)*
        anglePolynomialTest (angleEigenPolynomial κ m) θ else 0 := by
  unfold angleSpectralTerm
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  rw [angleSpectralFactor_pairing hκ]
  split_ifs with h
  · subst m
    rfl
  · exact mul_zero _

lemma angleSpectralKernel_pairing {κ u : ℝ} (hκ : 0<κ)
    (hu : angleSpectralMixingTime κ≤u) (θ : ℝ) (m : ℕ) :
    (∫ φ, angleSpectralKernel κ u θ φ*anglePolynomialTest (angleEigenPolynomial κ m) φ
      ∂Target.angleLaw κ)=Real.exp (-u*anglePolynomialEigenvalue κ m)*
        anglePolynomialTest (angleEigenPolynomial κ m) θ := by
  have : IsProbabilityMeasure (Target.angleLaw κ) := Target.angleLaw_isProbability hκ
  obtain ⟨M,hM⟩ := anglePolynomialTest_bound (angleEigenPolynomial κ m)
  have hM0 : 0≤M := (norm_nonneg _).trans (hM 0)
  let F := fun n φ => angleSpectralTerm κ u n θ φ*anglePolynomialTest (angleEigenPolynomial κ m) φ
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) (Target.angleLaw κ) :=
    ((angleSpectralTerm_measurable κ u n θ).mul
      ((angleEigenPolynomial κ m).continuous.comp Real.continuous_cos).measurable).aestronglyMeasurable
  have hb (n : ℕ) (φ : ℝ) : ‖F n φ‖≤(1/3:ℝ)^n*M := by
    dsimp [F]
    rw [abs_mul]
    exact mul_le_mul (angleSpectralTerm_bound_all hκ hu n θ φ) (hM φ)
      (abs_nonneg _) (by positivity)
  have hs : Summable (fun n : ℕ => (1/3:ℝ)^n*M) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/3)
      (by norm_num : (1/3:ℝ)<1)).mul_right M
  have hi : Integrable (fun _φ : ℝ => ∑' n : ℕ, (1/3:ℝ)^n*M) (Target.angleLaw κ) :=
    integrable_const _
  have hsum := hasSum_integral_of_dominated_convergence (fun (n : ℕ) (_φ : ℝ) => (1/3:ℝ)^n*M)
    hFm (fun n => Filter.Eventually.of_forall (hb n))
    (Filter.Eventually.of_forall (fun _φ => hs)) hi
    (show ∀ᵐ φ ∂Target.angleLaw κ, HasSum (fun n => F n φ)
      (angleSpectralKernel κ u θ φ*anglePolynomialTest (angleEigenPolynomial κ m) φ) from by
      apply Filter.Eventually.of_forall
      intro φ
      have hs' : Summable (fun n => angleSpectralTerm κ u n θ φ) :=
        (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/3)
          (by norm_num : (1/3:ℝ)<1)).of_norm_bounded
            (fun n => angleSpectralTerm_bound_all hκ hu n θ φ)
      simpa only [← angleSpectralKernel_eq_tsum hκ hu] using
        hs'.hasSum.mul_right (anglePolynomialTest (angleEigenPolynomial κ m) φ))
  rw [← hsum.tsum_eq]
  simp only [F,angleSpectralTerm_pairing hκ]
  simp

end SLEExactGauge

end

end OAI
