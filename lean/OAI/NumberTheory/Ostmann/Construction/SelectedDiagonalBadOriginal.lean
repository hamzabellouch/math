import OAI.NumberTheory.Ostmann.Construction.DiagonalEnvironmentAverage
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalSplit

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction
namespace InitialSourceChoice
open Conclusion
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (s l : ℕ) (X : ℝ)
local notation "b₀" => (bulkSize k L/2)
local notation "seed" => Template.initial (2*b₀) k
local notation "T" => Template.remainder (l+1) (Template.current seed l)
local notation "U" => Template.extracted (l+1) (Template.current seed l)
local notation "V" => frequencyBound Bs BD Bz k L
local notation "bins" => Arithmetic.sourceStateBins b₀ s C.bulkBin C.spectatorBin
local notation "Bad" => diagonalBadPermutation (2*b₀) k l

theorem bad_weighted_fixed_sum_extraction (outside : List ℕ) (p : ℕ)
    (u : SourceAssignment C.sources U) :
    ((((assignedSlots C.sources U u).map SmallSlot.value).prod:ℝ)*
      Ostmann.smoothPartition (Real.log p-C.giantCenter))*
      (∑e,if Bad e then fixedSmallCounterpartExpression d C.sources seed V C.giant X C.giantCenter
        bins outside l p u e else 0).re=
    C.selectedDiagonalNormalizer l*
      (∑e,(externalPivotWeight C.giantCenter p:ℂ)*
        (if Bad e then C.correctedSmallCounterpartExpression seed V X bins outside l
          (C.compensationLogScale l) (stepGap BD Bz k L l) p u e else 0)).re := by
  have h :
      (((((assignedSlots C.sources U u).map SmallSlot.value).prod:ℝ)*
        Ostmann.smoothPartition (Real.log p-C.giantCenter)):ℂ)*
        (∑e,if Bad e then fixedSmallCounterpartExpression d C.sources seed V C.giant X C.giantCenter
          bins outside l p u e else 0)=
      (C.selectedDiagonalNormalizer l:ℂ)*
        (∑e,(externalPivotWeight C.giantCenter p:ℂ)*
          (if Bad e then C.correctedSmallCounterpartExpression seed V X bins outside l
            (C.compensationLogScale l) (stepGap BD Bz k L l) p u e else 0)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hb : Bad e
    · simp only [ite_eq_left hb]
      rw [C.fixedSmallCounterpartExpression_scalar_extraction seed V X bins outside l
        (C.compensationLogScale l) (stepGap BD Bz k L l) (fun q hq => hq) p u e]
      simp only [selectedDiagonalNormalizer,Complex.ofReal_mul,mul_assoc]
    · simp only [ite_eq_right hb,mul_zero]
  have hh := congrArg Complex.re h
  simpa only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,add_zero,sub_zero] using hh

theorem selectedBadCovarianceSum_original (spectator : PrimeSource) :
    C.selectedDiagonalNormalizer l*(C.selectedBadCovarianceSum spectator s X l).re=
      (spectatorPrior spectator (2*s)).mean (fun ds =>
        (assignmentPrior C.sources U).mean (fun u =>
          ∑p∈integerPivotCell C.giantCenter,
            ((((assignedSlots C.sources U u).map SmallSlot.value).prod:ℝ)*
              Ostmann.smoothPartition (Real.log p-C.giantCenter))*
              (∑e,if Bad e then fixedSmallCounterpartExpression d C.sources seed V C.giant X C.giantCenter
                bins (spectatorList spectator ds) l p u e else 0).re)) := by
  symm
  simp_rw [C.bad_weighted_fixed_sum_extraction s l X]
  rw [finite_diagonal_environment_exchange]
  congr 1
  apply congrArg Complex.re
  unfold selectedBadCovarianceSum
  apply Finset.sum_congr rfl
  intro e he
  by_cases hb : Bad e
  · simp only [ite_eq_left hb]
    rfl
  · simp only [ite_eq_right hb,mul_zero,Finset.sum_const_zero,FinitePrior.cmean]

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
