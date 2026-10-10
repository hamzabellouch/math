import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalIndexedNormEventual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalMaskedMean

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord
open DiagonalEstimate ParityActions
attribute [local instance] Classical.propDecidable
section
variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ)

theorem sourceTerminalMaskedFactors_norms
    (σ τ : Reassignments k n (wordSize k ℓ))
    (masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ)
    (hm : ∀i q,‖masks i q‖≤1)
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ)))
    (r : ℤ) (t u : HistoryReconstruction.Tree (n+1)) (q v : ℕ)
    (hL : ‖sourceTerminalLongFactor w n σ τ p L S r t u q‖≤1)
    (hS : ‖sourceTerminalShortFactor w n σ τ p L S r t u v‖≤1) :
    ‖sourceTerminalMaskedLongFactor w n σ τ masks p L S r t u q‖≤1 ∧
    ‖sourceTerminalMaskedShortFactor w n σ τ masks p L S r t u v‖≤1 := by
  have hl : sourceTerminalMaskedLongFactor w n σ τ masks p L S r t u q =
      longCoordinateMask masks (fun i=>(p i).val) L S q * sourceTerminalLongFactor w n σ τ p L S r t u q := by
    unfold sourceTerminalMaskedLongFactor priorJoinLongUnary sourceTerminalLongFactor
    ring
  have hs : sourceTerminalMaskedShortFactor w n σ τ masks p L S r t u v =
      shortCoordinateMask masks S v * sourceTerminalShortFactor w n σ τ p L S r t u v := by
    unfold sourceTerminalMaskedShortFactor priorJoinShortUnary sourceTerminalShortFactor
    ring
  rw [hl,hs,norm_mul,norm_mul]
  exact ⟨(mul_le_mul (norm_longCoordinateMask_le masks hm (fun i=>(p i).val) L S q)
      hL (norm_nonneg _) zero_le_one).trans_eq (one_mul 1),
    (mul_le_mul (norm_shortCoordinateMask_le masks hm S v)
      hS (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)⟩

theorem sourceTerminalMaskedFactors_norms_of_mass {U : ℕ}
    (σ τ : Reassignments k n (wordSize k ℓ))
    (masks : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→ℕ→ℂ)
    (hm : ∀i q,‖masks i q‖≤1)
    (h h' : SourceHistory (k:=k) (L:=ℓ) (BD:=BD) (n+1)) (hroot : h.val.1=h'.val.1)
    (hrange : ∀path f,f∈ranges (BD+20*Real.log (depthScale k)) (wordSize k ℓ : ℝ) (n+1) path→
      f≠0 ∧ f.natAbs≤U)
    (hlarge : ∀i q,q∈sourceScheduledShells w (n+1) i→U<q.val)
    (p : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (hp : (productPrior (sourceTerminalCoordinatePrior w n)).mass p≠0)
    (L S : (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k ℓ))) :
    (∀q∈sourceScheduledShells w (n+1) L,
      ‖sourceTerminalMaskedLongFactor w n σ τ masks p L S h.val.1 h.val.2 h'.val.2 q.val‖≤1) ∧
    (∀q∈sourceScheduledShells w (n+1) S,
      ‖sourceTerminalMaskedShortFactor w n σ τ masks p L S h.val.1 h.val.2 h'.val.2 q.val‖≤1) := by
  have hn := sourceTerminalFactors_norms_of_mass w n σ τ h h' hroot hrange hlarge p hp L S
  have mul_bound {a b : ℂ} (ha : ‖a‖≤1) (hb : ‖b‖≤1) : ‖a*b‖≤1 := by
    rw [norm_mul]
    exact (mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  constructor
  · intro q hq
    have he : sourceTerminalMaskedLongFactor w n σ τ masks p L S h.val.1 h.val.2 h'.val.2 q.val =
        longCoordinateMask masks (fun i=>(p i).val) L S q.val * sourceTerminalLongFactor w n σ τ p L S h.val.1 h.val.2 h'.val.2 q.val := by
      unfold sourceTerminalMaskedLongFactor priorJoinLongUnary sourceTerminalLongFactor
      ring
    rw [he]
    exact mul_bound (norm_longCoordinateMask_le masks hm _ L S q.val) (hn.1 q hq)
  · intro q hq
    have he : sourceTerminalMaskedShortFactor w n σ τ masks p L S h.val.1 h.val.2 h'.val.2 q.val =
        shortCoordinateMask masks S q.val * sourceTerminalShortFactor w n σ τ p L S h.val.1 h.val.2 h'.val.2 q.val := by
      unfold sourceTerminalMaskedShortFactor priorJoinShortUnary sourceTerminalShortFactor
      ring
    rw [he]
    exact mul_bound (norm_shortCoordinateMask_le masks hm S q.val) (hn.2 q hq)
end
end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
