import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorReferences

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError
open Construction Conclusion CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkSourceDisintegration HistoryCompensationBiasedKernelSum
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def collisionPatternReferences (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (outside : List ℕ) (a : SelectedNonbulkSample C l)
    (refs : ∀p:Pattern τ,(Block p → CommonSample C.sources origin)  → 
      Option (PrincipalCollisionReference C outside a p)) :
    ∀p:Pattern τ,(Block p → CommonSample C.sources origin)  → 
      Option (PatternReference p (frequencyBound Bs BD Bz k L) outside l) :=
  fun p b => (refs p b).map PrincipalCollisionReference.patternReference

def collisionAmplitude (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (outside : List ℕ) (a : SelectedNonbulkSample C l)
    (refs : ∀p:Pattern τ,(Block p → CommonSample C.sources origin)  → 
      Option (PrincipalCollisionReference C outside a p))
    (corrected mixed : Bool) (u : SelectedBulkSample C l) (p : Pattern τ)
    (b : BlockDraw p (CommonSample C.sources origin)) : ℂ :=
  match refs p b.val with
  | none => 0
  | some r => r.value corrected mixed u

def collisionPrincipalMean (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (outside : List ℕ) (a : SelectedNonbulkSample C l)
    (refs : ∀p:Pattern τ,(Block p → CommonSample C.sources origin)  → 
      Option (PrincipalCollisionReference C outside a p))
    (mask : SelectedBulkSample C l  →  ∀p:Pattern τ,
      (Block p → CommonSample C.sources origin)  →  ℝ)
    (corrected mixed guarded : Bool) : ℂ :=
  let K := fun _ : SelectedBulkSample C l =>
    optionalDrawSymbolicPatternKernel C.sources origin τ mixed (frequencyBound Bs BD Bz k L)
      outside l (collisionPatternReferences C origin τ outside a refs)
  let amp := collisionAmplitude C origin τ outside a refs corrected mixed
  originalBulkPrincipalSum C.sources origin τ (selectedBulkPrior C l) mask
    (fun u p b => if guarded ∧ ¬fibreSmallOutsideGuard C outside a u then 0 else
      principalTest C.sources origin τ K amp u p b)

theorem collisionPrincipalMean_activeMask (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (outside : List ℕ) (a : SelectedNonbulkSample C l)
    (refs : ∀p:Pattern τ,(Block p → CommonSample C.sources origin)  → 
      Option (PrincipalCollisionReference C outside a p))
    (mask : SelectedBulkSample C l  →  ∀p:Pattern τ,
      (Block p → CommonSample C.sources origin)  →  ℝ)
    (corrected mixed guarded : Bool) :
    collisionPrincipalMean C origin τ outside a refs mask corrected mixed guarded =
      collisionPrincipalMean C origin τ outside a refs
        (fun u p b => if (refs p b).isSome then mask u p b else 0) corrected mixed guarded := by
  unfold collisionPrincipalMean originalBulkPrincipalSum
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  apply congrArg (selectedBulkPrior C l).cmean
  funext u
  cases hr : refs p b.val with
  | none =>
    simp only [Option.isSome_none,Bool.false_eq_true,ite_false,
      principalTest,collisionAmplitude,hr,zero_mul,Complex.ofReal_zero]
    split_ifs <;> simp only [mul_zero]
  | some r => simp only [hr,Option.isSome_some,ite_true]

end Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError

end

end OAI
