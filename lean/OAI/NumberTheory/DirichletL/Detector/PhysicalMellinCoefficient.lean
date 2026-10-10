import OAI.NumberTheory.DirichletL.Detector.PhysicalCoefficientScaling
import OAI.NumberTheory.DirichletL.Detector.MellinPowers

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma completedIndex_norm (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    elementNorm (completedIndex I J)=(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  rw [completedIndex, elementNorm_mul, elementNorm_pow]
  unfold elementNorm
  rw [(primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1,
    (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J hJ)).1]

theorem physical_mellin_coefficient (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (D I J : Ideal O) (η : HeckeFamily.Character) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime (calibrationForSet S hS).generator (completedIndex I J*s))
    (X : ℝ) (hX : 0<X) (H : O) (hH : H≠0) (t z : ℂ) :
    let C := calibrationForSet S hS
    let A := completedIndex I J
    let hA := supportedElement_ne_zero A (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*A):ℝ):ℂ)*actualCongruenceCoefficient C A s hA H *
      ((K*elementNorm H/elementNorm ((C.generator*A)*s)):ℂ)^(-z) =
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*completedMask S D I J*star (C.residueMonoid H)*
      bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I hI) A s hA H *
      (fullIdealWeight (t+1-z+1/2) I*fullIdealWeight (1+3*(t+1-z)) J) := by
  dsimp only
  have hA : Supported (Ideal.span {completedIndex I J}) := supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ)
  rw [physical_spectral_coefficient_scale S D I J η (calibrationForSet S hS) s hs hI hJ hsf
    hcop.of_mul_right_left X hX t H]
  rw [calibratedHighCoefficient_eq_bare S hS η I (supported_primaryGenerator_ne_zero I hI)
    (completedIndex I J) s hA hs hcop H]
  have hr := congrArg (fun r : ℝ => (r : ℂ)) (physical_radial_argument
    (calibrationForSet S hS).generator (completedIndex I J) s H X
    (elementNorm_pos _ (calibrationForSet S hS).generator_ne_zero).ne'
    (elementNorm_pos _ (supportedElement_ne_zero s hs)).ne')
  simp only [Complex.ofReal_div, Complex.ofReal_mul] at hr
  simp only [Complex.ofReal_mul]
  rw [hr]
  rw [completedIndex_norm I J hI hJ]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ.1)
  have hn := sourceNormPower_identity (Ideal.absNorm I) (Ideal.absNorm J) (elementNorm H) X
    hi hj (elementNorm_pos H hH) hX t z
  rw [show -(t+1-z)-1/2= -(t+1-z+1/2) by ring] at hn
  simp only [fullIdealWeight,hI.1,hJ.1,ite_false,Complex.ofReal_natCast,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow] at hn ⊢
  have he := congrArg (fun v : ℂ=>v*completedMask S D I J*
    star ((calibrationForSet S hS).residueMonoid H)*
    bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I hI) (completedIndex I J) s
      (supportedElement_ne_zero _ hA) H) hn
  convert he using 1 <;> ring_nf

end SevenEighths.ProbePhysical
end

end OAI
