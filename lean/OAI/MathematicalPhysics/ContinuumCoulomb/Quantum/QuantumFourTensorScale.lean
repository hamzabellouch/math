import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorComparison

namespace OAI

/-! Polynomial penalty scale for the full four-spin comparison. -/

noncomputable section
namespace ContinuumCoulomb

theorem qmaFourTensor_scale_bounds {b r v c e : ℝ} (hb : 1 ≤ b) (hr : 4*b ≤ r)
    (hv0 : 0 ≤ v) (hc0 : 0 ≤ c) (_he0 : 0 ≤ e) (hv : v ≤ b) (hc : c ≤ b) (he : e ≤ b) :
    2*(r*v+c+e+(v*c/(4*r)+c^2/(4*r^2))) ≤ 4*r^2 ∧
      2*(r*v+c+e+(v*c/(4*r)+c^2/(4*r^2)))*(v/(8*r)+c/(4*r^2))^2+
        (v*c/(4*r)+c^2/(4*r^2)) ≤ 9*b^3/r := by
  have hb0 : 0 ≤ b := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hvc : v*c ≤ b^2 := (mul_le_mul hv hc hc0 hb0).trans_eq (by ring)
  have hc2 : c^2 ≤ b^2 := pow_le_pow_left₀ hc0 hc 2
  have hden : 4*r ≤ 4*r^2 := by nlinarith
  have hδ : v*c/(4*r)+c^2/(4*r^2) ≤ b^2/r := by
    calc
      _ ≤ b^2/(4*r)+b^2/(4*r^2) := add_le_add
        (div_le_div_of_nonneg_right hvc (by positivity))
        (div_le_div_of_nonneg_right hc2 (by positivity))
      _ ≤ b^2/(4*r)+b^2/(4*r) := add_le_add le_rfl
        (div_le_div_of_nonneg_left (sq_nonneg b) (by positivity : 0 < 4*r) hden)
      _ = (b^2/r)/2 := by field_simp; ring
      _ ≤ b^2/r := by nlinarith [div_nonneg (sq_nonneg b) hr0.le]
  have hη : v/(8*r)+c/(4*r^2) ≤ b/r := by
    calc
      _ ≤ b/(8*r)+b/(4*r^2) := add_le_add
        (div_le_div_of_nonneg_right hv (by positivity))
        (div_le_div_of_nonneg_right hc (by positivity))
      _ ≤ b/(8*r)+b/(4*r) := add_le_add le_rfl
        (div_le_div_of_nonneg_left hb0 (by positivity : 0 < 4*r) hden)
      _ = 3/8*(b/r) := by field_simp; ring
      _ ≤ b/r := by nlinarith [div_nonneg hb0 hr0.le]
  have hδb : v*c/(4*r)+c^2/(4*r^2) ≤ b := hδ.trans (by
    apply (div_le_iff₀ hr0).mpr
    nlinarith)
  have hsum : r*v+c+e+(v*c/(4*r)+c^2/(4*r^2)) ≤ 4*b*r := by
    have hrv := mul_le_mul_of_nonneg_left hv hr0.le
    have hbr := mul_le_mul_of_nonneg_left hr1 hb0
    nlinarith
  constructor
  · have hbr := mul_le_mul_of_nonneg_left hr hr0.le
    nlinarith
  · have hη0 : 0 ≤ v/(8*r)+c/(4*r^2) := by positivity
    have hsq := pow_le_pow_left₀ hη0 hη 2
    have hmain : 2*(r*v+c+e+(v*c/(4*r)+c^2/(4*r^2)))*(v/(8*r)+c/(4*r^2))^2 ≤ 8*b^3/r := by
      calc
        _ ≤ (2*(4*b*r))*(b/r)^2 := mul_le_mul
          (mul_le_mul_of_nonneg_left hsum (by norm_num)) hsq (sq_nonneg _) (by positivity)
        _ = _ := by field_simp; ring
    have hb23 : b^2 ≤ b^3 := pow_le_pow_right₀ hb (by omega)
    have hδ3 := hδ.trans (div_le_div_of_nonneg_right hb23 hr0.le)
    exact (add_le_add hmain hδ3).trans_eq (by ring)

open Matrix
open scoped InnerProductSpace Classical
variable {n : ℕ}

theorem qmaFourTensor_polynomial_comparison (r b : ℝ) (hb : 1 ≤ b) (hr : 4*b ≤ r)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hVs : V.conjTranspose = V) (hCs : C.conjTranspose = C)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (hH : qmaFourTensorPenalty n*(V*qmaFourTensorEncoding n) = (8:ℂ) • (V*qmaFourTensorEncoding n))
    (hVn : ‖spinMatrixOperator V‖ ≤ b) (hCn : ‖spinMatrixOperator C‖ ≤ b)
    (hNn : ‖spinMatrixOperator (qmaFourTensorEffectiveMatrix V C)‖ ≤ b)
    (u : EuclideanSpace ℂ (Fin n → Fin 2)) (hu : ‖u‖ = 1) :
    |MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix r ((r:ℂ) • V+C))-
      MediatorGraph.normalizedBottom (qmaFourTensorEffectiveMatrix V C)| ≤ 9*b^3/r := by
  have hb0 : 0 ≤ b := by linarith
  have hr0 : 0 < r := by linarith
  have hs := qmaFourTensor_scale_bounds hb hr hb0 hb0 (norm_nonneg _)
    (le_refl b) (le_refl b) hNn
  exact (qmaFourTensor_comparison r hr0 V C hVs hCs hV hH hb0 hb0 hVn hCn u hu hs.1).trans hs.2

theorem qmaFourTensor_polynomial_accuracy (b : ℝ) (hb : 1 ≤ b)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hVs : V.conjTranspose = V) (hCs : C.conjTranspose = C)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (hH : qmaFourTensorPenalty n*(V*qmaFourTensorEncoding n) = (8:ℂ) • (V*qmaFourTensorEncoding n))
    (hVn : ‖spinMatrixOperator V‖ ≤ b) (hCn : ‖spinMatrixOperator C‖ ≤ b)
    (hNn : ‖spinMatrixOperator (qmaFourTensorEffectiveMatrix V C)‖ ≤ b)
    (u : EuclideanSpace ℂ (Fin n → Fin 2)) (hu : ‖u‖ = 1) (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix (9*b^3*N) (((9*b^3*N:ℝ):ℂ) • V+C))-
      MediatorGraph.normalizedBottom (qmaFourTensorEffectiveMatrix V C)| ≤ 1/(N:ℝ) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hb0 : 0 < b := by linarith
  have hb13 : b ≤ b^3 := by simpa only [pow_one] using pow_le_pow_right₀ hb (show 1 ≤ 3 by omega)
  have hlarge : 4*b ≤ 9*b^3*N := by nlinarith [mul_le_mul_of_nonneg_left hN1 (by positivity : 0 ≤ 9*b^3)]
  have h := qmaFourTensor_polynomial_comparison (9*b^3*N) b hb hlarge V C hVs hCs hV hH hVn hCn hNn u hu
  have he : 9*b^3/(9*b^3*N) = 1/(N:ℝ) := by field_simp
  rwa [he] at h

end ContinuumCoulomb

end

end OAI
