import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinMasks

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

def priorJoinLongUnary (D : I→I→ℤ) (p : I→ℕ)
    (χ : I→(q:ℕ)→MulChar (ZMod q) ℂ) (ν masks : I→ℕ→ℂ)
    (L S : I) (q : ℕ) : ℂ :=
  longPrimeSupportMask p L S q * longCoordinateMask masks p L S q *
    indexedLongUnary D p χ ν L S q

def priorJoinShortUnary (D : I→I→ℤ) (p : I→ℕ)
    (χ : I→(q:ℕ)→MulChar (ZMod q) ℂ) (ν masks : I→ℕ→ℂ)
    (L S : I) (r : ℕ) : ℂ :=
  shortPrimeSupportMask p L S r * shortCoordinateMask masks S r *
    indexedShortUnary D p χ ν L S r

theorem masked_survivingPhasePair_twoPrimeAssignment (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ)
    (L S : SurvivingPrimeIndex k j width) (hLS : L≠S) (q r : ℕ)
    [∀i,Fact (twoPrimeAssignment p L S q r i).Prime] (hqr : q.Coprime r)
    (χ : SurvivingPrimeIndex k j width → (q:ℕ)→MulChar (ZMod q) ℂ)
    (a : SurvivingPrimeIndex k j width → (q:ℕ)→ZMod q)
    (ζ masks : SurvivingPrimeIndex k j width → ℕ→ℂ)
    (P : ℕ) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (positive : Bool)
    (hforward : survivingDifferenceGraph k j hj width σ ρ S L=if positive then 2 else -2)
    (hrev : survivingDifferenceGraph k j hj width σ ρ L S=0) :
    (if Pairwise (fun i v=>(twoPrimeAssignment p L S q r i).Coprime
          (twoPrimeAssignment p L S q r v)) then
        (∏i,masks i (twoPrimeAssignment p L S q r i))*
          survivingPhasePair k j hj width σ ρ (twoPrimeAssignment p L S q r) χ a ζ P s t u
      else 0) =
      priorJoinLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ
        (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) masks L S q *
      priorJoinShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ
        (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) masks L S r *
      exposedCharacter (χ S r) positive q := by
  have hg := twoPrimeAssignment_support_indicator_of_coprime p L S hLS q r hqr
  by_cases hc : Pairwise (fun i v=>(twoPrimeAssignment p L S q r i).Coprime
      (twoPrimeAssignment p L S q r v))
  · have hg' : longPrimeSupportMask p L S q*shortPrimeSupportMask p L S r=1 := by
      simpa only [ite_eq_left hc] using hg.symm
    have hp := survivingPhasePair_twoPrimeAssignment k j hj width σ ρ p L S hLS q r hc χ a ζ P s t u hrev
    rw [ite_eq_left hc,coordinateMaskProduct_twoPrimeAssignment masks p L S hLS q r,hp]
    rw [hforward,←exposedCharacter_apply]
    unfold priorJoinLongUnary priorJoinShortUnary
    calc
      _ = (longPrimeSupportMask p L S q*shortPrimeSupportMask p L S r)*
          ((longCoordinateMask masks p L S q*shortCoordinateMask masks S r)*
            (indexedLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ
              (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S q *
             indexedShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ
              (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S r *
             exposedCharacter (χ S r) positive q)) := by rw [hg',one_mul]
      _ = _ := by ring
  · have hg' : longPrimeSupportMask p L S q*shortPrimeSupportMask p L S r=0 := by
      simpa only [ite_eq_right hc] using hg.symm
    rw [ite_eq_right hc]
    unfold priorJoinLongUnary priorJoinShortUnary
    calc
      _ = (longPrimeSupportMask p L S q*shortPrimeSupportMask p L S r)*
          ((longCoordinateMask masks p L S q*shortCoordinateMask masks S r)*
            (indexedLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ
              (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S q *
             indexedShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ
              (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S r *
             exposedCharacter (χ S r) positive q)) := by rw [hg',zero_mul]
      _ = _ := by ring

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
