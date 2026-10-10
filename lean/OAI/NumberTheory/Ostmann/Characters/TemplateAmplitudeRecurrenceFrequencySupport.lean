import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceFrequencySum
import OAI.NumberTheory.Ostmann.Construction.JoinedRemaining

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.RetainedRow
open Construction HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

section
variable {α γ : Type*} [Fintype α] [Fintype γ]
    (k j : ℕ) (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (μ : FinitePrior α) (ν : FinitePrior γ) (h : α → CopiedState k j)
    (y : γ → OutsideState k j) (S : List Bool → Finset ℤ) (path : List Bool)
    (R : Finset ℕ+) (phase : γ → ℕ+ → α → SupportedHistory S j path → ℂ)

theorem offDiagonal_frequency_sum_support (hj:j<k) (hprod : ∀x,(∏i,h x i)≠0)
    (T : Finset ℤ)
    (hcut : ∀a,ν.mass a≠0 → ∀x x',μ.mass x≠0 → μ.mass x'≠0 →
      ∀(z z':SupportedHistory S j path),∀P∈R,∀s:ℤ,
      z.val.1*(∏i,h x' i)-z'.val.1*(∏i,h x i)≠0 →
      z.val.1*(∏i,h x' i)-z'.val.1*(∏i,h x i)=s*(P:ℤ) →
      pairCoefficient k j B V extra mask X Δ W h y S path phase a x x' z z' P≠0 → s∈T) :
    offDiagonal k j B V extra mask X Δ W μ ν h y S path R phase =
      ν.cmean (fun a => μ.cmean (fun x => μ.cmean (fun x' =>
        ∑z:SupportedHistory S j path,∑z':SupportedHistory S j path,∑s∈T,
          frequencyPairCoefficient k j B V extra mask X Δ W h y S path R phase T a x x' z z' s))) := by
  rw [offDiagonal_pair_pivot_sum k j B V extra mask X Δ W μ ν h y S path R phase hj hprod]
  apply FinitePrior.cmean_congr_support
  intro a ha
  apply FinitePrior.cmean_congr_support
  intro x hx
  apply FinitePrior.cmean_congr_support
  intro x' hx'
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro z' hz'
  simpa only [copiedProduct_pairedState,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,
    frequencyPairCoefficient] using reconstructedPivot_positive_subtype_reindex k j
      (pairedState k j (h x) (h x') (y a)) z.val.1 z'.val.1 R T
      (pairCoefficient k j B V extra mask X Δ W h y S path phase a x x' z z')
      (by simpa only [copiedProduct_pairedState,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false]
          using hcut a ha x x' hx hx' z z')

end
end Ostmann.Characters.Template.RetainedRow

end

end OAI
