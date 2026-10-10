import Mathlib
import OAI.Analysis.Conductivity.Fourier.FourierPairFlux
import OAI.Analysis.Conductivity.Fourier.LeadingFrequencyAlignment

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma normalizedAngularTensor_quadratic (s : Fin 3 → ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℝ) :
    normalizedAngularTensor s A 0*x^2+2*normalizedAngularTensor s A 1*x*y+
      normalizedAngularTensor s A 2*y^2=
      angularNormalization A *
        (s 0*((A 1 1:ℝ)*x-(A 1 0:ℝ)*y)^2+
          2*s 1*((A 1 1:ℝ)*x-(A 1 0:ℝ)*y)*(-(A 0 1:ℝ)*x+(A 0 0:ℝ)*y)+
          s 2*(-(A 0 1:ℝ)*x+(A 0 0:ℝ)*y)^2) := by
  dsimp [normalizedAngularTensor]
  ring

lemma angular_vecMul_zero (h : Fin 2 → ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ((h ᵥ* A) 0:ℝ)=(h 0:ℝ)*(A 0 0:ℝ)+(h 1:ℝ)*(A 1 0:ℝ) := by
  simp [Matrix.vecMul,dotProduct,Fin.sum_univ_two]

lemma angular_vecMul_one (h : Fin 2 → ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ((h ᵥ* A) 1:ℝ)=(h 0:ℝ)*(A 0 1:ℝ)+(h 1:ℝ)*(A 1 1:ℝ) := by
  simp [Matrix.vecMul,dotProduct,Fin.sum_univ_two]

lemma angular_vecMul_inverse {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (h : Fin 2 → ℤ) :
    (A 1 1:ℝ)*((h ᵥ* A) 0:ℝ)-(A 1 0:ℝ)*((h ᵥ* A) 1:ℝ)=(h 0:ℝ) ∧
    -(A 0 1:ℝ)*((h ᵥ* A) 0:ℝ)+(A 0 0:ℝ)*((h ᵥ* A) 1:ℝ)=(h 1:ℝ) := by
  have hdZ : A 0 0*A 1 1-A 0 1*A 1 0=1 := by simpa only [det_fin_two] using hA
  have hd : (A 0 0:ℝ)*(A 1 1:ℝ)-(A 0 1:ℝ)*(A 1 0:ℝ)=1 := by exact_mod_cast hdZ
  rw [angular_vecMul_zero,angular_vecMul_one]
  constructor
  · calc
      _ = ((A 0 0:ℝ)*(A 1 1:ℝ)-(A 0 1:ℝ)*(A 1 0:ℝ))*(h 0:ℝ) := by ring
      _ = _ := by rw [hd,one_mul]
  · calc
      _ = ((A 0 0:ℝ)*(A 1 1:ℝ)-(A 0 1:ℝ)*(A 1 0:ℝ))*(h 1:ℝ) := by ring
      _ = _ := by rw [hd,one_mul]

lemma torusQuadratic_angular_conjugacy (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) (h : Fin 2 → ℤ) :
    torusQuadratic (normalizedAngularTensor s A) (h ᵥ* A)=
      angularNormalization A*torusQuadratic s h := by
  unfold torusQuadratic
  rw [normalizedAngularTensor_quadratic,(angular_vecMul_inverse hA h).1,
    (angular_vecMul_inverse hA h).2]

lemma torusRate_angular_conjugacy (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) (h : Fin 2 → ℤ) :
    torusRate (normalizedAngularTensor s A) (h ᵥ* A)=
      Real.sqrt (angularNormalization A)*torusRate s h := by
  unfold torusRate
  rw [torusQuadratic_angular_conjugacy s hA,
    Real.sqrt_mul (angularNormalization_pos A).le]

def angularNormalizedLift (A : Matrix (Fin 2) (Fin 2) ℤ) (x : Coord3) : Coord3 :=
  ![Real.sqrt (angularNormalization A)*x 0,
    (A 0 0:ℝ)*x 1+(A 0 1:ℝ)*x 2,(A 1 0:ℝ)*x 1+(A 1 1:ℝ)*x 2]

lemma torusAngular_normalizedLift (h : Fin 2 → ℤ)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (x : Coord3) :
    torusAngular h (angularNormalizedLift A x)=torusAngular (h ᵥ* A) x := by
  simp only [torusAngular,_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  rw [angular_vecMul_zero,angular_vecMul_one]
  dsimp [angularNormalizedLift]
  ring

theorem flatPhaseMode_angular_conjugacy (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (h : Fin 2 → ℤ) (phase : ℝ) (x : Coord3) :
    flatPhaseMode s h phase (angularNormalizedLift A x)=
      flatPhaseMode (normalizedAngularTensor s A) (h ᵥ* A) phase x := by
  unfold flatPhaseMode
  rw [torusAngular_normalizedLift,torusRate_angular_conjugacy s hA]
  congr 2
  dsimp [angularNormalizedLift]
  ring

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

def angularInverseMatrix (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![A 1 1,-A 0 1;-A 1 0,A 0 0]

lemma angular_mul_inverse {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) :
    A*angularInverseMatrix A=1 := by
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by simpa only [det_fin_two] using hA
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,angularInverseMatrix] <;> nlinarith

lemma angular_inverse_mul {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) :
    angularInverseMatrix A*A=1 := by
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by simpa only [det_fin_two] using hA
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,angularInverseMatrix] <;> nlinarith

def angularFrequencyEquiv (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det=1) :
    (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun h := h ᵥ* A
  invFun h := h ᵥ* angularInverseMatrix A
  left_inv h := by
    change (h ᵥ* A) ᵥ* angularInverseMatrix A=h
    rw [vecMul_vecMul,angular_mul_inverse hA,vecMul_one]
  right_inv h := by
    change (h ᵥ* angularInverseMatrix A) ᵥ* A=h
    rw [vecMul_vecMul,angular_inverse_mul hA,vecMul_one]

@[simp] lemma angularFrequencyEquiv_apply (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A.det=1) (h : Fin 2 → ℤ) : angularFrequencyEquiv A hA h=h ᵥ* A := rfl

@[simp] lemma angularFrequencyEquiv_symm_vecMul (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A.det=1) (h : Fin 2 → ℤ) :
    (angularFrequencyEquiv A hA).symm (h ᵥ* A)=h :=
  (angularFrequencyEquiv A hA).symm_apply_apply h

theorem flatFourier_angular_conjugacy (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (a phase : (Fin 2 → ℤ) → ℝ) (x : Coord3) :
    flatFourier s a phase (angularNormalizedLift A x)=
      flatFourier (normalizedAngularTensor s A)
        (a ∘ (angularFrequencyEquiv A hA).symm)
        (phase ∘ (angularFrequencyEquiv A hA).symm) x := by
  unfold flatFourier
  conv_rhs => rw [←(angularFrequencyEquiv A hA).tsum_eq]
  apply tsum_congr
  intro h
  simp only [Function.comp_apply,angularFrequencyEquiv_apply,angularFrequencyEquiv_symm_vecMul]
  rw [flatPhaseMode_angular_conjugacy s hA]

lemma normalizedFourierCoefficients_angular_conjugacy (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (a : (Fin 2 → ℤ) → ℝ) (lam T : ℝ) (h : Fin 2 → ℤ) :
    normalizedFourierCoefficients (normalizedAngularTensor s A)
      (Real.sqrt (angularNormalization A)*lam) T
      (a ∘ (angularFrequencyEquiv A hA).symm) (angularFrequencyEquiv A hA h)=
    normalizedFourierCoefficients s lam (Real.sqrt (angularNormalization A)*T) a h := by
  simp only [normalizedFourierCoefficients,Function.comp_apply,
    angularFrequencyEquiv_apply,angularFrequencyEquiv_symm_vecMul,torusRate_angular_conjugacy s hA]
  congr 2
  ring

lemma angular_conjugacy_gap (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    {a : (Fin 2 → ℤ) → ℝ} {lam gap : ℝ}
    (hgap : 0<gap) (hr : ∀ h,a h≠0 → lam+gap≤torusRate s h) :
    0<Real.sqrt (angularNormalization A)*gap ∧
      ∀ h,(a ∘ (angularFrequencyEquiv A hA).symm) h≠0 →
        Real.sqrt (angularNormalization A)*lam+Real.sqrt (angularNormalization A)*gap≤
          torusRate (normalizedAngularTensor s A) h := by
  have hm : 0<Real.sqrt (angularNormalization A) := Real.sqrt_pos.mpr (angularNormalization_pos A)
  refine ⟨mul_pos hm hgap,?_⟩
  intro h hh
  obtain ⟨g,rfl⟩ := (angularFrequencyEquiv A hA).surjective h
  simp only [Function.comp_apply,Equiv.symm_apply_apply] at hh
  rw [angularFrequencyEquiv_apply,torusRate_angular_conjugacy s hA]
  simpa only [mul_add] using mul_le_mul_of_nonneg_left (hr g hh) hm.le

end ScalarConductivity

end

end OAI
