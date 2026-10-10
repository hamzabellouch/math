import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorActualDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkPrincipalCollisionError HistoryBulkActualPrincipalCollisionPattern
open HistoryBulkSourceDisintegration HistoryBulkUniversalPatternAggregation
open HistoryCompensationBiasedKernelSum HistoryPairKernelReplacement
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def referenceKernel (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (outside : List ℕ) (a : SelectedNonbulkSample C l)
    {p : Pattern τ} (r : PrincipalCollisionReference C outside a p)
    (b : Block p → CommonSample C.sources origin) (mixed : Bool) : ℂ :=
  ((∏q : Block p,symbolicKernel mixed r.amplitude.left r.amplitude.right
    r.amplitude.leftSupported r.amplitude.rightSupported (r.representative q) (b q).val : ℝ):ℂ)

theorem collisionPrincipalMean_eq_pattern (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (outside : List ℕ) (a : SelectedNonbulkSample C l)
    (refs : ∀p:Pattern τ,(Block p → CommonSample C.sources origin) →
      Option (PrincipalCollisionReference C outside a p))
    (mask : SelectedBulkSample C l → ∀p:Pattern τ,
      (Block p → CommonSample C.sources origin) → ℝ)
    (corrected mixed guarded : Bool) :
    collisionPrincipalMean C origin τ outside a refs mask corrected mixed guarded =
      patternComplexSum C.sources origin τ (fun p b=> (refs p b).elim 0 (fun r=>
        referenceKernel C origin τ outside a r b mixed *
          (selectedBulkPrior C l).cmean (fun u=> (mask u p b:ℂ)*
            (if guarded ∧ ¬fibreSmallOutsideGuard C outside a u then 0 else
              r.value corrected mixed u)))) := by
  unfold collisionPrincipalMean
  dsimp only
  unfold principalTest collisionAmplitude
  let test := fun (u : SelectedBulkSample C l) (p : Pattern τ)
      (b : Block p → CommonSample C.sources origin) =>
    if guarded ∧ ¬fibreSmallOutsideGuard C outside a u then (0:ℂ) else
      (match refs p b with | none => 0 | some r => r.value corrected mixed u) *
        ((∏q,optionalDrawSymbolicPatternKernel C.sources origin τ mixed
          (frequencyBound Bs BD Bz k L) outside l
          (collisionPatternReferences C origin τ outside a refs) p b q:ℝ):ℂ)
  change originalBulkPrincipalSum C.sources origin τ (selectedBulkPrior C l) mask
    (fun u p b=>test u p b.val)=_
  rw [originalBulkPrincipalSum_eq_patternComplexSum C.sources origin τ (selectedBulkPrior C l) mask test]
  dsimp only [test]
  apply congrArg (patternComplexSum C.sources origin τ)
  funext p b
  cases hr : refs p b with
  | none =>
    simp only [Option.elim_none,zero_mul]
    simp only [ite_self,mul_zero,FinitePrior.cmean,Finset.sum_const_zero]
  | some r =>
    simp only [Option.elim_some,
      collisionPatternReferences,optionalDrawSymbolicPatternKernel,hr,Option.map_some,
      PrincipalCollisionReference.patternReference]
    rw [←FinitePrior.cmean_mul_left]
    apply congrArg (selectedBulkPrior C l).cmean
    funext u
    dsimp only [referenceKernel]
    split_ifs <;> ring

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
