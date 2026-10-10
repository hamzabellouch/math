import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorActualDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError
open Construction Conclusion CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkSourceDisintegration HistoryCompensationBiasedKernelSum
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

theorem originalBulkPrincipalSum_scale (sources : SourceFamily) (origin τ : ι → ℕ)
    (μ : FinitePrior Ω)
    (mask : Ω → ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ)
    (test : Ω → ∀p:Pattern τ,BlockDraw p (CommonSample sources origin) → ℂ) (c : ℂ) :
    originalBulkPrincipalSum sources origin τ μ mask (fun u p b => c*test u p b) =
      c*originalBulkPrincipalSum sources origin τ μ mask test := by
  simp only [originalBulkPrincipalSum,FinitePrior.cmean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro u hu
  ring

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem collisionPrincipalMean_scaledTest (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (outside : List ℕ) (a : SelectedNonbulkSample C l)
    (refs : ∀p:Pattern τ,(Block p → CommonSample C.sources origin) →
      Option (PrincipalCollisionReference C outside a p))
    (mask : SelectedBulkSample C l → ∀p:Pattern τ,
      (Block p → CommonSample C.sources origin) → ℝ)
    (corrected mixed guarded : Bool) (c : ℂ) :
    let K := fun _ : SelectedBulkSample C l =>
      optionalDrawSymbolicPatternKernel C.sources origin τ mixed (frequencyBound Bs BD Bz k L)
        outside l (collisionPatternReferences C origin τ outside a refs)
    let amp := collisionAmplitude C origin τ outside a refs corrected mixed
    originalBulkPrincipalSum C.sources origin τ (selectedBulkPrior C l) mask
      (fun u p b => if guarded ∧ ¬fibreSmallOutsideGuard C outside a u then 0 else
        principalTest C.sources origin τ K (fun u p b => c*amp u p b) u p b) =
      c*collisionPrincipalMean C origin τ outside a refs mask corrected mixed guarded := by
  dsimp only
  unfold collisionPrincipalMean
  rw [←originalBulkPrincipalSum_scale]
  apply congrArg (originalBulkPrincipalSum C.sources origin τ (selectedBulkPrior C l) mask)
  funext u p b
  by_cases hg : guarded ∧ ¬fibreSmallOutsideGuard C outside a u
  · simp [hg]
  · simp [hg,principalTest,mul_assoc]

theorem collisionPrincipalMean_true (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (outside : List ℕ) (a : SelectedNonbulkSample C l)
    (refs : ∀p:Pattern τ,(Block p → CommonSample C.sources origin) →
      Option (PrincipalCollisionReference C outside a p))
    (mask : SelectedBulkSample C l → ∀p:Pattern τ,
      (Block p → CommonSample C.sources origin) → ℝ)
    (corrected mixed : Bool) :
    collisionPrincipalMean C origin τ outside a refs mask corrected mixed true =
    let K := fun _ : SelectedBulkSample C l =>
      optionalDrawSymbolicPatternKernel C.sources origin τ mixed (frequencyBound Bs BD Bz k L)
        outside l (collisionPatternReferences C origin τ outside a refs)
    let amp := collisionAmplitude C origin τ outside a refs corrected mixed
    originalBulkPrincipalSum C.sources origin τ (selectedBulkPrior C l) mask
      (fun u p b => if fibreSmallOutsideGuard C outside a u then
        principalTest C.sources origin τ K amp u p b else 0) := by
  unfold collisionPrincipalMean
  apply congrArg (originalBulkPrincipalSum C.sources origin τ (selectedBulkPrior C l) mask)
  funext u p b
  by_cases hg : fibreSmallOutsideGuard C outside a u <;> simp [hg]

theorem collisionPrincipalMean_false (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (outside : List ℕ) (a : SelectedNonbulkSample C l)
    (refs : ∀p:Pattern τ,(Block p → CommonSample C.sources origin) →
      Option (PrincipalCollisionReference C outside a p))
    (mask : SelectedBulkSample C l → ∀p:Pattern τ,
      (Block p → CommonSample C.sources origin) → ℝ)
    (corrected mixed : Bool) :
    collisionPrincipalMean C origin τ outside a refs mask corrected mixed false =
    let K := fun _ : SelectedBulkSample C l =>
      optionalDrawSymbolicPatternKernel C.sources origin τ mixed (frequencyBound Bs BD Bz k L)
        outside l (collisionPatternReferences C origin τ outside a refs)
    originalBulkPrincipalSum C.sources origin τ (selectedBulkPrior C l) mask
      (principalTest C.sources origin τ K (collisionAmplitude C origin τ outside a refs corrected mixed)) := by
  unfold collisionPrincipalMean
  apply congrArg (originalBulkPrincipalSum C.sources origin τ (selectedBulkPrior C l) mask)
  funext u p b
  simp only [Bool.false_eq_true,false_and,ite_false]

end Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError

end

end OAI
