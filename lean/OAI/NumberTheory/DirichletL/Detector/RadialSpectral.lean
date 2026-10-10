import OAI.NumberTheory.DirichletL.Detector.RadialIdentity
import OAI.NumberTheory.DirichletL.Detector.SpectralPoisson

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma spectralSummand_mask_nonzero (S : Finset Id) (D I J : Id) (Ψ : O→*ℂ) (t : ℂ)
    (h : spectralSummand S D Ψ t I J≠0) : completedMask S D I J≠0 := by
  intro hz
  exact h (by simp only [spectralSummand,hz,zero_mul])

lemma spectralSummand_calibration_coprime (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D I J : Id) (Ψ : O→*ℂ) (t : ℂ) (h : spectralSummand S D Ψ t I J≠0) :
    IsCoprime (calibrationForSet S hS).generator (completedIndex I J) := by
  have hm := spectralSummand_mask_nonzero S D I J Ψ t h
  have hA : completedIndex I J≠0 := by
    intro hz
    exact h (spectralSummand_zero_completedIndex S D I J Ψ t hz)
  have hout : ∀P∈S,¬P∣I*J^3 := by
    unfold completedMask at hm
    split_ifs at hm with hd
    · exact hd.2
    · exact False.elim (hm rfl)
  apply calibrationForSet_coprime_of_excluded S hS
  rw [completedIndex_eq_primaryGenerator] at hA ⊢
  rw [(primaryGenerator_spec (I*J^3) hA).1]
  exact hout

def radialMellinSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset Id) (D : Id) (s : O) (hs : Supported (Ideal.span {s}))
    (W : SchwartzMap ℝ ℂ) (K σ : ℝ) (t : ℂ) (I J : Id) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C (completedIndex I J) s hA H.val*
          ((K*elementNorm H.val/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)*
            mellin (paperRadialFourier W) z)
  else 0

theorem transformedSpectralTerm_radial_mellin (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty) (D : Id)
    (s : O) (hs : Supported (Ideal.span {s})) (hcs : IsCoprime (calibrationForSet S hS).generator s)
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W⊆Set.Icc a b)
    (K σ : ℝ) (hK : 0<K) (hσ : 1<σ) (t : ℂ) (I J : Id) :
    transformedSpectralTerm η (calibrationForSet S hS) S D s hs W K t I J=
      radialMellinSpectralTerm η (calibrationForSet S hS) S D s hs W K σ t I J := by
  unfold transformedSpectralTerm radialMellinSpectralTerm
  split_ifs with hA
  · by_cases hz : spectralSummand S D (baseRowCoefficient η (calibrationForSet S hS).Xi s hs) t I J=0
    · simp only [hz,zero_mul]
    · rw [actualFrequency_mellin S hS hSne (completedIndex I J) s hA (supportedElement_ne_zero s hs)
        ((spectralSummand_calibration_coprime S hS D I J _ t hz).mul_right hcs)
        W a b ha hW K hK σ hσ]
  · rfl

end SevenEighths.ProbePhysical
end

end OAI
