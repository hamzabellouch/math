import OAI.NumberTheory.Ostmann.Construction.DiagonalEnvironmentAverage
import OAI.NumberTheory.Ostmann.Construction.DiagonalEnvironmentTerms

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (seed : List SourceSlot)
    (V : ℕ→ℕ) (spectator : PrimeSource) (m : ℕ) (X : ℝ)
    (bins : List ℕ→State→ℝ) (l : ℕ) (B Δ : ℝ)
local notation "T" => Template.remainder (l+1) (Template.current seed l)
local notation "U" => Template.extracted (l+1) (Template.current seed l)

def diagonalCovariance (e : Equiv.Perm (RemainingIndex T)) : ℂ :=
  (spectatorPrior spectator m).cmean (fun ds =>
    (assignmentPrior C.sources U).cmean (fun u =>
      ∑p∈integerPivotCell C.giantCenter,(externalPivotWeight C.giantCenter p:ℂ)*
        C.correctedSmallCounterpartExpression seed V X bins (spectatorList spectator ds) l B Δ p u e))

theorem weighted_fixed_sum_extraction
    (hseed : ∀q∈seed,q∈Template.initial (2*(Conclusion.bulkSize k L/2)) k)
    (outside : List ℕ) (p : ℕ) (u : SourceAssignment C.sources U) :
    ((((assignedSlots C.sources U u).map SmallSlot.value).prod:ℝ)*
      Ostmann.smoothPartition (Real.log p-C.giantCenter))*
      (∑e : Equiv.Perm (RemainingIndex T),
        fixedSmallCounterpartExpression d C.sources seed V C.giant X C.giantCenter bins outside l p u e).re=
    (C.remainingNormalization T*Real.exp (-Δ))*
      (∑e : Equiv.Perm (RemainingIndex T),(externalPivotWeight C.giantCenter p:ℂ)*
        C.correctedSmallCounterpartExpression seed V X bins outside l B Δ p u e).re := by
  have h :
      (((((assignedSlots C.sources U u).map SmallSlot.value).prod:ℝ)*
        Ostmann.smoothPartition (Real.log p-C.giantCenter)):ℂ)*
        (∑e : Equiv.Perm (RemainingIndex T),
          fixedSmallCounterpartExpression d C.sources seed V C.giant X C.giantCenter bins outside l p u e)=
      ((C.remainingNormalization T*Real.exp (-Δ)):ℂ)*
        (∑e : Equiv.Perm (RemainingIndex T),(externalPivotWeight C.giantCenter p:ℂ)*
          C.correctedSmallCounterpartExpression seed V X bins outside l B Δ p u e) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [C.fixedSmallCounterpartExpression_scalar_extraction seed V X bins outside l B Δ hseed p u e]
    simp only [mul_assoc]
  have hh := congrArg Complex.re h
  simpa only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,add_zero,sub_zero] using hh

theorem extendedDiagonal_le_covariances
    (hseed : ∀q∈seed,q∈Template.initial (2*(Conclusion.bulkSize k L/2)) k)
    (hg : C.giant.AboveFrequency (V l))
    (hs : ∀i : Fin (T).length,(C.sources T[i].origin).AboveFrequency (V l))
    (hsep : RemainingBandsSeparated C.sources T C.giant) :
    extendedDiagonal d C.favorable C.sources seed V C.giant spectator m X C.giantCenter bins l≤
      (C.remainingNormalization T*Real.exp (-Δ))*
        (∑e : Equiv.Perm (RemainingIndex T),C.diagonalCovariance seed V spectator m X bins l B Δ e).re := by
  calc
    _ ≤ (spectatorPrior spectator m).mean (fun ds =>
        (assignmentPrior C.sources U).mean (fun u =>
          ∑p∈integerPivotCell C.giantCenter,
            ((((assignedSlots C.sources U u).map SmallSlot.value).prod:ℝ)*
              Ostmann.smoothPartition (Real.log p-C.giantCenter))*
            (∑e : Equiv.Perm (RemainingIndex T),
              fixedSmallCounterpartExpression d C.sources seed V C.giant X C.giantCenter bins
                (spectatorList spectator ds) l p u e).re)) := by
      apply FinitePrior.mean_mono
      intro ds
      apply FinitePrior.mean_mono
      intro u
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (remainingDiagonal_le_fixed_counterpart_sum d C.sources seed V C.giant X C.giantCenter bins
          (spectatorList spectator ds) l p u C.favorable hg hs hsep)
        (mul_nonneg (Nat.cast_nonneg _) (Ostmann.smoothPartition_nonneg _))
    _ = _ := by
      simp_rw [C.weighted_fixed_sum_extraction seed V X bins l B Δ hseed]
      exact finite_diagonal_environment_exchange (spectatorPrior spectator m)
        (assignmentPrior C.sources U) (integerPivotCell C.giantCenter)
        (externalPivotWeight C.giantCenter) (C.remainingNormalization T*Real.exp (-Δ))
        (fun e ds u p => C.correctedSmallCounterpartExpression seed V X bins
          (spectatorList spectator ds) l B Δ p u e)

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
