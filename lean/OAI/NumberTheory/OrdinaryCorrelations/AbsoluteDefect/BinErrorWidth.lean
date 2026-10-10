import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AssignedLength
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BinnedStage
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicCofactorMellinEqPolynomial
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BinSumByMultiples
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BinnedRamareErrorIdentity
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeCountZeroIff

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace SourcePrimeFactor
open OrdinaryCorrelations OrdinaryDirichletMeanSquare OrdinaryNarrowGrid Finset

def binErrorWidth (q r R X : ℕ) : ℕ := X/q+2*(q*2^(r+R))

def dyadicCharacterPolynomial (f : ℕ → ℂ) {d : ℕ} (χ : DirichletCharacter ℂ d)
    (X : ℕ) (t : ℝ) : ℂ :=
  polynomial (Ioc X (2*X)) (fun n => characterModulation f χ n/(n:ℂ)) (fun n => Real.log n) t

lemma binnedStage_identity (f : ℕ → ℂ) {d : ℕ} (χ : DirichletCharacter ℂ d)
    (q r R X : ℕ) (hq : 0<q) (t : ℝ) :
    binnedStage f χ q r R X t=
      polynomial (Ioc 0 (2*(X+binErrorWidth q r R X)))
        (fun n => OrdinaryCorrelations.SourcePrimeFactor.binnedRamareCoefficient
          (primeWindow q r R) (assignedLength q r R X) (characterModulation f χ) n/(n:ℂ))
        (fun n => Real.log n) t := by
  have hp : ∀p∈primeWindow q r R,0<p :=
    fun p hp => ((mem_filter.mp hp).2).pos
  have hU : ∀p∈primeWindow q r R,p*(2*assignedLength q r R X p)≤2*(X+binErrorWidth q r R X) := by
    intro p hp
    have hh := (assigned_length_cutoff q r R X hq hp).2
    nlinarith
  rw [OrdinaryCorrelations.SourcePrimeFactor.binnedRamare_polynomial_bins
    (grid q r R) primeBin (primeWindow q r R) hp (prime_window_bins q r R)
    (prime_bins_disjoint q r R hq) (assignedLength q r R X) (evenBinLength X)
    (fun i hi p hp => assigned_length_eq q r R X hq hi hp)
    (characterModulation f χ) (2*(X+binErrorWidth q r R X)) hU t]
  unfold binnedStage
  apply sum_congr rfl
  intro i hi
  rw [dyadicCofactorMellin_eq_polynomial]
  rfl

lemma binnedStage_error_identity (f : ℕ → ℂ) {d : ℕ} (χ : DirichletCharacter ℂ d)
    (q r R X : ℕ) (hq : 0<q) (t : ℝ) :
    binnedStage f χ q r R X t-dyadicCharacterPolynomial f χ X t=
      polynomial (Ioc (X-binErrorWidth q r R X) (2*(X+binErrorWidth q r R X)))
        (fun n => OrdinaryCorrelations.SourcePrimeFactor.binnedRamareError
          (primeWindow q r R) (assignedLength q r R X) (characterModulation f χ) X n/(n:ℂ))
        (fun n => Real.log n) t := by
  rw [binnedStage_identity f χ q r R X hq t]
  apply OrdinaryCorrelations.SourcePrimeFactor.binnedRamare_error_identity
  intro p hp
  have hh := assigned_length_cutoff q r R X hq hp
  exact ⟨hh.1,hh.2.trans (Nat.le_add_right _ _)⟩

theorem binnedStage_sampled_error {f : ℕ → ℂ} (hf : OneBounded f) (hm : Multiplicative f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) (q r R X : ℕ) (hq : 0<q) (hX : 0<X)
    (hE : 2*binErrorWidth q r R X≤X)
    (S : Finset ℝ) {T : ℝ} (hT : 0≤T)
    (hS : ∀t∈S,t∈Set.Icc (-T) T) (hsep : ∀t∈S,∀u∈S,t≠u → 1≤|t-u|) :
    (∑t∈S,‖binnedStage f χ q r R X t-dyadicCharacterPolynomial f χ X t‖^2) ≤
    (4*Real.exp (1+1/4)*gaussianConstant*(T+1+2*((X:ℝ)+binErrorWidth q r R X))*(2+(Real.log 6)^2))*
      (4*(4*((X:ℝ)+binErrorWidth q r R X)*Real.exp (-(∑p∈primeWindow q r R,(p:ℝ)⁻¹))+
        (4*((q*2^(r+R):ℕ):ℝ))^8+
        2*((X:ℝ)+binErrorWidth q r R X)*(∑p∈primeWindow q r R,(p:ℝ)⁻¹^2)+
        6*(binErrorWidth q r R X:ℝ))/((X-binErrorWidth q r R X:ℕ):ℝ)^2) := by
  simp_rw [binnedStage_error_identity f χ q r R X hq]
  have hp : ∀p∈primeWindow q r R,Nat.Prime p := fun p hp => (mem_filter.mp hp).2
  have he := OrdinaryCorrelations.SourcePrimeFactor.binnedRamare_sampled_error
    (primeWindow q r R) hp (assignedLength q r R X)
    (characterModulation_bound hf χ) (characterModulation_multiplicative hm χ)
    X (binErrorWidth q r R X) hX hE
    (fun p hp => ⟨(assigned_length_cutoff q r R X hq hp).1,
      (assigned_length_cutoff q r R X hq hp).2.trans (Nat.le_add_right _ _)⟩)
    S hT hS hsep
  apply he.trans
  have ha := OrdinaryCorrelations.SourcePrimeFactor.ramareArithmeticExceptions_card
    (primeWindow q r R) hp (X-binErrorWidth q r R X) (2*(X+binErrorWidth q r R X))
  have hr := OrdinaryWindowEuler.prime_window_rough (primeWindow q r R)
    (Nat.mul_pos hq (by positivity)) (prime_window_subset q r R) (2*(X+binErrorWidth q r R X))
  push_cast at ha hr
  apply mul_le_mul_of_nonneg_left _ (by unfold gaussianConstant; positivity)
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  push_cast
  nlinarith

end SourcePrimeFactor

end

end OAI
