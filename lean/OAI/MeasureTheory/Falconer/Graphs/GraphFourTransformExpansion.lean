import OAI.MeasureTheory.Falconer.Fourier.GraphKernelBounds
import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def sourceGraphFourTransform
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (r : ℝ) (u v : UnitCircle) : ℂ :=
  W (u,v) *
    (sourceAngularTransform (ρ 0) (X 0) (M 0) (b 0) r u *
      conj (sourceAngularTransform (ρ 1) (X 1) (M 1) (b 1) r u)) *
    (sourceAngularTransform (ρ 2) (X 2) (M 2) (b 2) r v *
      conj (sourceAngularTransform (ρ 3) (X 3) (M 3) (b 3) r v))

theorem graphFourKernel_endpoint_product
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (r : ℝ) (u v : UnitCircle) (x : Fin 4 → Plane) :
    graphFourKernel b W x r u v = W (u,v) *
      ∏ i : Fin 4, (![fun y => sourcePlaneWave r u y * b 0 y u,
        fun y => conj (sourcePlaneWave r u y * b 1 y u),
        fun y => sourcePlaneWave r v y * b 2 y v,
        fun y => conj (sourcePlaneWave r v y * b 3 y v)] i) (x i) := by
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, graphFourKernel, graphFourAmplitude,
    ← sourcePlaneWave_sub, map_mul]
  ring

theorem sourceGraphFourTransform_endpoint_integral
    (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (r : ℝ) (u v : UnitCircle) :
    sourceGraphFourTransform ρ X M b W r u v =
      ((M 0*M 1)*(M 2*M 3))⁻¹ •
        (∫ x, graphFourKernel b W x r u v ∂Measure.pi (fun i => (ρ i).restrict (X i))) := by
  simp_rw [graphFourKernel_endpoint_product, integral_const_mul]
  rw [integral_fintype_prod_eq_prod]
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [integral_conj]
  simp only [sourceGraphFourTransform, sourceAngularTransform, sourcePlaneWave,
    Complex.real_smul, map_mul, map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv,
    Complex.ofReal_mul, mul_inv_rev]
  ring

theorem sourceGraphFourTransform_profile_normalization
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane)
    (Mp Ma : Fin 4 → ℝ) (hM : ∀ i, Mp i ≠ 0) (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (r : ℝ) (u v : UnitCircle) :
    sourceGraphFourTransform ρ X Ma b W r u v =
      ((Mp 0/Ma 0)*(Mp 1/Ma 1)*(Mp 2/Ma 2)*(Mp 3/Ma 3)) •
        sourceGraphFourTransform ρ X Mp b W r u v := by
  simp only [sourceGraphFourTransform, sourceAngularTransform, Complex.real_smul,
    map_mul, map_inv₀, Complex.conj_ofReal, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_inv]
  have h0 : (Mp 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM 0)
  have h1 : (Mp 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM 1)
  have h2 : (Mp 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM 2)
  have h3 : (Mp 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM 3)
  field_simp

end PlanarFalconer

end OAI
