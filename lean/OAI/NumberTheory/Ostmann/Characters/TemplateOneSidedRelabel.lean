import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePrefix
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedRelabelSampled
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedRelabelSlice

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedRelabel
open SymbolicHistory TemplateOneSidedCancellation Template TemplateOneSidedBudget
open ParityActions OneSidedPhase Preliminaries
attribute [local instance] Classical.propDecidable

def paritySampledExpressions (k n : ℕ) (width : Role → ℕ) (m : ℕ)
    (hm : m ≤ width .word) (σ : Reassignments k n m) :
    Expressions (ι:=(schedule k (n+1)).Constituent width) k (n+1) :=
  permutedSampledExpressions k (n+1) width (prefixConstituentPermutation k n width m hm σ)

theorem paritySampledExpressions_prime_eval (k n : ℕ) (width : Role → ℕ) (m : ℕ)
    (hm : m ≤ width .word) (σ : Reassignments k n m) {Q : ℕ}
    (a : (schedule k (n+1)).Constituent width → PrimeUpTo Q) :
    evalExpressions (fun i=>(a i).val) (paritySampledExpressions k n width m hm σ) =
      constituentSampleState (schedule k (n+1)) width
        (constituentAssignment (schedule k (n+1)) width
          (prefixConstituentPermutation k n width m hm σ) a) :=
  permutedSampledExpressions_prime_eval k (n+1) width _ a

theorem parityPair_residueModulus (k n : ℕ) (width : Role → ℕ) (m : ℕ)
    (hm : m ≤ width .word) (σ ρ : Reassignments k n m) (s r : ℤ)
    (t u : HistoryReconstruction.Tree (n+1)) :
    residueModulus (historyResidueGuards k (n+1) s (paritySampledExpressions k n width m hm σ) t) *
      residueModulus (historyResidueGuards k (n+1) r (paritySampledExpressions k n width m hm ρ) u) =
    residueModulus (historyResidueGuards k (n+1) s (sampledExpressions k (n+1) width) t) *
      residueModulus (historyResidueGuards k (n+1) r (sampledExpressions k (n+1) width) u) := by
  exact congrArg₂ (·*·)
    (permutedSampledResidueModulus k (n+1) width _ s t)
    (permutedSampledResidueModulus k (n+1) width _ r u)

theorem permutedSampled_profileValue (k j : ℕ) (width : Role → ℕ)
    (π : Equiv.Perm ((schedule k j).Constituent width)) (b : Bool) (s : ℤ)
    (t : HistoryReconstruction.Tree j) (i : Fin (2^j))
    (a : (schedule k j).Constituent width → ℤ) (X : ℝ) :
    profileValue k X (evalBottom k a
      (indexedBottomExpressions k j b s (permutedSampledExpressions k j width π) t i)) =
    profileValue k X (evalBottom k (fun r=>a (π.symm r))
      (indexedBottomExpressions k j b s (sampledExpressions k j width) t i)) := by
  simp only [permutedSampledExpressions,indexedBottomExpressions_relabel,evalBottom_relabel]

theorem permutedSampled_leafData_degreeCost (k j : ℕ) (width : Role → ℕ)
    (π : Equiv.Perm ((schedule k j).Constituent width)) (m : ℕ) (hw : ∀r,width r ≤ m)
    (B0 V0 : ℕ → ℤ)
    (g : (l : ℕ) → ℤ → List (Guard (schedule k l).Slot)) (Gcount Gsize : ℕ)
    (hc : ∀l s,(g l s).length ≤ Gcount)
    (hg : ∀l s,∀q∈g l s,q.expression.syntaxSize ≤ Gsize)
    (b : Bool) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (i : (schedule k j).Constituent width)
    (x : TemplateSupportRemoval.Other i → ℤ) (X A B : ℝ) :
    (leafData k
      (fun q : Fin (historyGuards k B0 V0 g j s (permutedSampledExpressions k j width π) t).length=>
        (historyGuards k B0 V0 g j s (permutedSampledExpressions k j width π) t).get q)
      (fun q : Fin (bottomExpressions k j b s (permutedSampledExpressions k j width π) t).length=>
        (bottomExpressions k j b s (permutedSampledExpressions k j width π) t).get q) i x X A B).degreeCost ≤
      2*(guardCountFactor k j*(Gcount+1)+3*2^j)*
        ((recursiveSizeFactor k j*(Gsize+1)+obstructionSizeFactor k j)*(2*(m+1)+1))+1 := by
  apply canonical_leafData_degreeCost k j B0 V0 g Gcount Gsize hc hg b s _ t (2*(m+1))
  intro r
  exact (permutedSampledExpressions_syntaxSize k j width π r).trans
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (hw _) 1))

end Ostmann.Characters.TemplateOneSidedRelabel

end

end OAI
