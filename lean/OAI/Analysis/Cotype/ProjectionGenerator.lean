import OAI.Analysis.Cotype.ComplexProjectionSpectrum
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem complexSpectralEval_const {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (c : ℂ) :
    complexSpectralEval P (fun _ => c) = c • 1 := by
  rw [← complexSpectralEval_one P]
  ext vector dual
  simp [complexSpectralEval, Finset.mul_sum]

def complexProjectionSpectralHom {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j)) :
    (Cube m → ℂ) →ₐ[ℂ] (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) where
  toFun := complexSpectralEval P
  map_zero' := by
    ext vector dual
    simp [complexSpectralEval]
  map_one' := complexSpectralEval_one P
  map_add' f g := by
    ext vector dual
    simp [complexSpectralEval, add_mul, Finset.sum_add_distrib]
  map_mul' f g := (complexSpectralEval_mul P hp hc f g).symm
  commutes' c := by
    change complexSpectralEval P (fun _ => c) = _
    rw [complexSpectralEval_const, Algebra.algebraMap_eq_smul_one]

def projectionGenerator {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y :=
  complexSpectralEval P (fun ε => (projectionDegree ε : ℂ))

def complexProjectionTime {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (t : ℂ) :
    ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y :=
  complexProjectionPolynomial P (Complex.exp (-t))

theorem complexProjectionTime_eq_exp {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j)) (t : ℂ) :
    complexProjectionTime P t = NormedSpace.exp ((-t) • projectionGenerator P) := by
  let H := complexProjectionSpectralHom P hp hc
  have hH : Continuous H := H.toLinearMap.continuous_of_finiteDimensional
  change complexProjectionTime P t = NormedSpace.exp ((-t) • H (fun ε => (projectionDegree ε : ℂ)))
  rw [← map_smul, ← NormedSpace.map_exp H hH]
  rw [complexProjectionTime, complexProjectionPolynomial_spectral]
  change complexSpectralEval P _ = complexSpectralEval P _
  congr 1
  funext ε
  simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem complexProjectionTime_real {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (t : ℝ) :
    complexProjectionTime P (t : ℂ) =
      complexDualLift (projectionSemigroup P (Real.exp (-t))) := by
  unfold complexProjectionTime
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, complexProjectionPolynomial_real]

theorem complexProjectionTime_real_norm_le {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hP : ∀ i y, ‖P i y‖ ≤ ‖y‖) {t : ℝ} (ht : 0 ≤ t) :
    ‖complexProjectionTime P (t : ℂ)‖ ≤ 1 := by
  rw [complexProjectionTime_real, complexDualLift_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  simpa only [one_mul] using projectionSemigroup_contracts P hP
    (Real.exp_pos (-t)).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)) y

theorem complexProjectionTime_real_power_gap {N : ℕ} {C : ℝ} (hC : 0 ≤ C)
    {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hgap : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ y : Y,
      ‖((1-projectionSemigroup P r)^N) y‖ ≤ C*‖y‖) {t : ℝ} (ht : 0 ≤ t) :
    ‖(1-complexProjectionTime P (t : ℂ))^N‖ ≤ C := by
  rw [complexProjectionTime_real]
  have h := ContinuousLinearMap.opNorm_le_bound _ hC
    (hgap (Real.exp (-t)) (Real.exp_pos (-t)).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)))
  simpa only [← complexDualLift_one, ← complexDualLift_sub, ← complexDualLift_pow,
    complexDualLift_norm] using h

end Cotype

end

end OAI
