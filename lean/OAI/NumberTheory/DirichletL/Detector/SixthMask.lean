import OAI.NumberTheory.DirichletL.Detector.SixthDecomposition
import OAI.NumberTheory.DirichletL.Detector.SpectralSupport

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve CubicEisenstein
open HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O

lemma calibration_sixth_ideal_mask (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (L : Ideal O) :
    (calibrationForSet S hS).residueMonoid (idealGenerator L)^6=
      if ∀P∈S,¬P∣L then 1 else 0 := by
  by_cases hL : ∀P∈S,¬P∣L
  · rw [ite_eq_left hL]
    apply calibrationForSet_residue_sixth
    apply calibrationForSet_coprime_of_excluded
    simpa only [span_idealGenerator] using hL
  · rw [ite_eq_right hL]
    have hz : (calibrationForSet S hS).residueMonoid (idealGenerator L)=0 := by
      by_contra hn
      have hu := (calibrationForSet S hS).residue.apply_ne_zero_iff.mp hn
      have hc := (isUnit_quotient_span_iff (calibrationForSet S hS).generator (idealGenerator L)).mp hu
      have ho := (calibrationForSet_coprime_iff S hS (idealGenerator L)).mp hc
      apply hL
      intro P hP hd
      apply ho P hP
      apply (Ideal.dvd_iff_le.mp hd)
      have hm : idealGenerator L∈Ideal.span ({idealGenerator L}:Set O) := Ideal.subset_span (by simp)
      rw [span_idealGenerator L] at hm
      exact hm
    rw [hz,zero_pow (by decide : 6≠0)]

lemma calibration_sixth_frequency_mask (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (u : O) (L : Ideal O) :
    star ((calibrationForSet S hS).residueMonoid (u*idealGenerator L^6))=
      star ((calibrationForSet S hS).residueMonoid u)*(if ∀P∈S,¬P∣L then 1 else 0) := by
  rw [map_mul,map_pow,calibration_sixth_ideal_mask]
  split_ifs <;> simp only [mul_one,mul_zero,star_zero]

lemma sixthFrequencyWeight (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (z : ℂ) :
    frequencyWeight z (sixthFrequencyEquiv p)=
      frequencyWeight z ⟨p.1.val,p.1.property.1⟩*fullIdealWeight (6*z) p.2.val := by
  have hu : 0<elementNorm p.1.val := elementNorm_pos _ p.1.property.1
  have hl : 0<(Ideal.absNorm p.2.val:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.2.property)
  have hn : elementNorm (sixthFrequencyEquiv p).val=
      elementNorm p.1.val*(Ideal.absNorm p.2.val:ℝ)^6 := by
    unfold elementNorm
    exact_mod_cast rowMap_norm p
  simp only [frequencyWeight,fullIdealWeight,ite_eq_right p.2.property,hn,Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hu.le (pow_nonneg hl.le 6)]
  congr 1
  have he := Complex.cpow_mul_ofReal_nonneg hl.le (6:ℝ) (-z)
  simp only [Real.rpow_ofNat,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_natCast] at he
  simp only [Complex.ofReal_pow,Complex.ofReal_natCast]
  rw [←he]
  congr 1
  ring

end SevenEighths.ProbePhysical
end

end OAI
