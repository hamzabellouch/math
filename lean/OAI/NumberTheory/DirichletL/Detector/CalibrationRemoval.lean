import OAI.NumberTheory.DirichletL.Detector.FrequencySupport
import OAI.NumberTheory.DirichletL.Detector.PhysicalReopen

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
open CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

lemma sexticGauss_unit_scale (s : O) (hs : Supported (Ideal.span {s}))
    (b h : O) (hcop : IsCoprime b s) :
    sexticGauss s (supportedElement_ne_zero s hs) (b*h) =
      (idealRowHom b (Ideal.span {s}))⁻¹ * sexticGauss s (supportedElement_ne_zero s hs) h := by
  let := finite_quotient_span (supportedElement_ne_zero s hs)
  let : Fintype (Residue s) := Fintype.ofFinite _
  let χ := supportedModulusCharacter s hs
  let ψ := quotientTrace s (supportedElement_ne_zero s hs)
  let u := residueUnit s b hcop.symm
  have he := gaussSum_mulShift_eq χ (ψ.mulShift (Ideal.Quotient.mk _ h)) u
  simp only [gaussSum, AddChar.mulShift_apply, MulChar.inv_apply_eq_inv', u, residueUnit_coe,
    χ, supportedModulusCharacter_mk] at he
  rw [← residueGauss_supported_mk s hs (b*h), ← residueGauss_supported_mk s hs h]
  simp only [residueGauss, tsum_fintype, map_mul]
  simpa only [ψ, mul_assoc, mul_comm, mul_left_comm] using he

lemma movingQuotient_unit_scale (A s : O) (hs : Supported (Ideal.span {s}))
    (b : O) (hcop : IsCoprime b s) (x : Residue (A*s)) :
    movingQuotient A s (supportedElement_ne_zero s hs) (Ideal.Quotient.mk _ b*x) =
      idealRowHom b (Ideal.span {A}) * (idealRowHom b (Ideal.span {s}))⁻¹ *
        movingQuotient A s (supportedElement_ne_zero s hs) x := by
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, movingQuotient_mk, movingQuotient_mk, idealRowHom_argument_mul]
  rw [show -(b*m)=b*(-m) by ring, sexticGauss_unit_scale s hs b (-m) hcop]
  ring

def barePhysicalFourier (A s : O) (hA : A≠0) (hs : s≠0) (H : O) : ℂ :=
  elementFourier (A*s) (mul_ne_zero hA hs)
    (fun m => idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H

theorem actualPhysicalFourier_calibration_factor (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0)
    (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    let C := calibrationForSet S hS
    actualPhysicalFourier C A s hA (supportedElement_ne_zero s hs) H =
      (C.residueMonoid (A*s) * star (C.residueMonoid H) *
        (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        idealRowHom C.generator (Ideal.span {A}) * (idealRowHom C.generator (Ideal.span {s}))⁻¹) *
      barePhysicalFourier A s hA (supportedElement_ne_zero s hs) H := by
  dsimp only
  let C := calibrationForSet S hS
  have hcs : IsCoprime C.generator s := hcop.of_mul_right_right
  rw [physicalFourier_eq_mixed, calibration_mixed_fourier S hS (A*s)
    (mul_ne_zero hA (supportedElement_ne_zero s hs)) hcop]
  dsimp only [C] at hcs ⊢
  simp_rw [movingQuotient_unit_scale A s hs (calibrationForSet S hS).generator hcs]
  simp only [mul_assoc, tsum_mul_left]
  rfl

def bareCongruenceCoefficient (A s : O) (hA : A≠0) (H : O) : ℂ :=
  congruenceCoefficient A s hA (outerQuotient A) (outerQuotient s) H

lemma barePhysicalFourier_eq (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    barePhysicalFourier A s hA hs H =
      (Ideal.absNorm (Ideal.span {s}):ℂ)*bareCongruenceCoefficient A s hA H := by
  unfold bareCongruenceCoefficient
  rw [← fullFourier_eq_congruence A s hA hs]
  unfold barePhysicalFourier elementFourier fullFourier
  apply tsum_congr
  intro m
  rw [rawFourier_outer]
  have he : conductorReduction A s m = Ideal.Quotient.mk (Ideal.span {A}) (representative (A*s) m) := by
    conv_lhs => rw [← representative_spec (A*s) m]
    rfl
  rw [he]
  unfold outerQuotient
  rw [sexticGauss_coefficient_mk]

theorem actualCongruenceCoefficient_calibration_factor (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0)
    (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    let C := calibrationForSet S hS
    actualCongruenceCoefficient C A s hA H =
      (C.residueMonoid (A*s) * star (C.residueMonoid H) *
        (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        idealRowHom C.generator (Ideal.span {A}) * (idealRowHom C.generator (Ideal.span {s}))⁻¹) *
      bareCongruenceCoefficient A s hA H := by
  dsimp only
  have he := actualPhysicalFourier_calibration_factor S hS A s hA hs hcop H
  dsimp only at he
  rw [actualPhysicalFourier_eq, barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  apply mul_left_cancel₀ hn
  rw [he]
  ring

end SevenEighths.ProbePhysical
end

end OAI
