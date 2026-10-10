import OAI.NumberTheory.DirichletL.Detector.SpectralSupport
import OAI.NumberTheory.DirichletL.Detector.HighAbsolute
import OAI.NumberTheory.DirichletL.Detector.IdealUnit

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def physicalMellinCoefficientTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (X : ℝ) (H : O) (t z : ℂ) : ℂ :=
  if hA : completedIndex I J≠0 then
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ)*
      actualCongruenceCoefficient C (completedIndex I J) s hA H *
      ((K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)
  else 0

def guardedHighMellinCoefficient (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J : Ideal O) (s : O) (X : ℝ) (H : O) (x z : ℂ) : ℂ :=
  if h : Squarefree I ∧ Supported I ∧ Supported J then
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*completedMask S D I J*star (C.residueMonoid H)*
      bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I h.2.1)
        (completedIndex I J) s (supportedElement_ne_zero _ (supported_completed _ _
          ((supported_span_primaryGenerator_iff I).mpr h.2.1)
          ((supported_span_primaryGenerator_iff J).mpr h.2.2))) H *
      (fullIdealWeight (x+1/2) I*fullIdealWeight (1+3*x) J)
  else 0

theorem physicalMellinCoefficientTerm_eq_guarded (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (D I J : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (hcs : IsCoprime (calibrationForSet S hS).generator s)
    (X : ℝ) (hX : 0<X) (H : O) (hH : H≠0) (t z : ℂ) :
    physicalMellinCoefficientTerm η (calibrationForSet S hS) S D I J s hs X H t z=
      guardedHighMellinCoefficient η (calibrationForSet S hS) S D I J s X H (t+1-z) z := by
  by_cases hg : Squarefree I ∧ Supported I ∧ Supported J
  · have hA : completedIndex I J≠0 := supportedElement_ne_zero _ (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hg.2.1)
      ((supported_span_primaryGenerator_iff J).mpr hg.2.2))
    rw [physicalMellinCoefficientTerm,dite_eq_left hA,guardedHighMellinCoefficient,dite_eq_left hg]
    dsimp only
    by_cases hm : completedMask S D I J=0
    · simp only [spectralSummand,hm,zero_mul,mul_zero]
    · have hc : IsCoprime (calibrationForSet S hS).generator (completedIndex I J) := by
        apply calibrationForSet_coprime_of_excluded S hS
        rw [completedIndex_eq_primaryGenerator] at hA ⊢
        rw [(primaryGenerator_spec (I*J^3) hA).1]
        unfold completedMask at hm
        split_ifs at hm with hd
        · exact hd.2
        · exact False.elim (hm rfl)
      exact physical_mellin_coefficient S hS D I J η s hs hg.2.1 hg.2.2 hg.1
        (hc.mul_right hcs) X hX H hH t z
  · have hz : spectralSummand S D (baseRowCoefficient η (calibrationForSet S hS).Xi s hs) t I J=0 := by
      by_contra hn
      exact hg (spectralSummand_support S hbad D I J _ t hn)
    rw [guardedHighMellinCoefficient,dite_eq_right hg]
    unfold physicalMellinCoefficientTerm
    split_ifs <;> simp only [hz,mul_zero,zero_mul]

theorem guardedHighMellinCoefficient_eq_high (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (D I J K : Ideal O)
    (hK : Supported K) (hKS : ∀P∈S,¬P∣K) (X : ℝ) (H : O) (x w z : ℂ) :
    guardedHighMellinCoefficient η C S D I J (primaryGenerator K) X H x z *
      fullIdealWeight w K =
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*star (C.residueMonoid H)*
      markedIdealHighSummand S D η H x w z I J K 1 := by
  have h1 : ∀P∈S,¬P∣(1:Ideal O) := by
    intro P hP hd
    exact (hS P hP).not_isUnit (isUnit_of_dvd_one hd)
  have hw : fullIdealWeight (6*z) (1:Ideal O)=1 := (IdealEuler.normWeight (6*z)).map_one
  unfold guardedHighMellinCoefficient markedIdealHighSummand highIdealMask
    bareIdealHighSummand bareIdealHighCoefficient
  simp only [ite_eq_left hKS,ite_eq_left h1,mul_one,hw,primaryGenerator_one,one_pow]
  by_cases hg : Squarefree I ∧ Supported I ∧ Supported J
  · have hfull : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O) :=
      ⟨hg.1,hg.2.1,hg.2.2,hK,supported_one_ideal⟩
    rw [dite_eq_left hg,dite_eq_left hfull]
    dsimp only [completedIndex]
    ring
  · have hfull : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O)) :=
      fun h=>hg ⟨h.1,h.2.1,h.2.2.1⟩
    rw [dite_eq_right hg,dite_eq_right hfull]
    simp only [mul_zero,zero_mul]

end SevenEighths.ProbePhysical
end

end OAI
