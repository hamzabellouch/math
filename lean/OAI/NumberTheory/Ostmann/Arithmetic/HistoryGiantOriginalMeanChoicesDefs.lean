import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCompensationErrorAverage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantOriginalMeanApproximation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantOriginalMeanCompensation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryGiantOriginalMeanFactorization
open Construction Conclusion HistoryGiantReferenceMean HistoryGiantChoiceMass
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
variable (s t : ℤ) (c e : Choices (l:=l) C)

structure PrimeReference where
  draw : PrimeDraw C.giant
  positive_weight : 0 < primeWeight C.giant draw
  left_supported : (history C x s (primeP C.giant draw) (primeQ C.giant draw) c).Supported
    (frequencyBound Bs BD Bz k L) outside
  right_supported : (history C y t (primeP C.giant draw) (primeQ C.giant draw) e).Supported
    (frequencyBound Bs BD Bz k L) outside

def primeReferenceMain (hout : ∀q∈outside,q.Prime)
    (r : Option (PrimeReference C outside x y s t c e)) : ℂ :=
  match r with
  | none => 0
  | some r => compensationFactor C x y s t c e *
      primeMainTerm C outside _ _ r.left_supported r.right_supported hout (k+2)

structure MixedReference where
  draw : MixedDraw C.giantCenter C.giant
  positive_weight : 0 < mixedWeight C.giantCenter C.giant draw
  left_supported : (history C x s (mixedP C.giantCenter C.giant draw) (mixedQ C.giantCenter C.giant draw) c).Supported
    (frequencyBound Bs BD Bz k L) outside
  right_supported : (history C y t (mixedP C.giantCenter C.giant draw) (mixedQ C.giantCenter C.giant draw) e).Supported
    (frequencyBound Bs BD Bz k L) outside

def mixedReferenceMain (hout : ∀q∈outside,q.Prime)
    (r : Option (MixedReference C outside x y s t c e)) : ℂ :=
  match r with
  | none => 0
  | some r => compensationFactor C x y s t c e *
      mixedMainTerm C outside _ _ r.left_supported r.right_supported hout (k+2)

def choicesPairSum (F : Choices (l:=l) C → Choices (l:=l) C → ℂ) : ℂ :=
  ∑ c : Choices (l:=l) C, ∑ e : Choices (l:=l) C,
    ((choicesMass C.sources _ _ l c * choicesMass C.sources _ _ l e : ℝ):ℂ)*F c e

theorem choicesPairSum_error_le
    (F G : Choices (l:=l) C → Choices (l:=l) C → ℂ)
    (B : Choices (l:=l) C → Choices (l:=l) C → ℝ)
    (h : ∀c e, choicesMass C.sources _ _ l c≠0 → choicesMass C.sources _ _ l e≠0 →
      ‖F c e-G c e‖≤B c e) :
    ‖choicesPairSum C F-choicesPairSum C G‖ ≤
      ∑c : Choices (l:=l) C, ∑e : Choices (l:=l) C,
        choicesMass C.sources _ _ l c*choicesMass C.sources _ _ l e*B c e := by
  classical
  have heq : choicesPairSum C F-choicesPairSum C G =
      ∑c : Choices (l:=l) C, ∑e : Choices (l:=l) C,
        ((choicesMass C.sources _ _ l c*choicesMass C.sources _ _ l e:ℝ):ℂ)*(F c e-G c e) := by
    simp only [choicesPairSum,mul_sub,Finset.sum_sub_distrib]
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  by_cases hc : choicesMass C.sources _ _ l c=0
  · simp only [hc,zero_mul,Complex.ofReal_zero,norm_zero,le_refl]
  by_cases he : choicesMass C.sources _ _ l e=0
  · simp only [he,mul_zero,zero_mul,Complex.ofReal_zero,norm_zero,le_refl]
  have hμ := mul_nonneg (choicesMass_nonneg C.sources _ _ l c)
    (choicesMass_nonneg C.sources _ _ l e)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hμ]
  exact mul_le_mul_of_nonneg_left (h c e hc he) hμ

end Ostmann.Arithmetic.HistoryGiantOriginalMeanFactorization

end

end OAI
