import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalEnd
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalEstimate
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalStart

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale Filter
attribute [local instance] Classical.propDecidable

theorem exists_eventually_sourceHistoryPairMean_sub_core (k : ℕ)
    {α β ρ γ c₀ c BD : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) (hBD : 0 ≤ BD) :
    ∃K : ℝ,0 < K ∧ ∀ᶠ L : ℝ in atTop,
    ∀(d : Decomposition)(E : Finset ℕ)(δ : ℝ),(∀p∈E,p.Prime) →
      (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀j (hj : j < k) (B V : ℕ → ℤ),∀P∈DiagonalEstimate.sourcePivotRanges w j,
      ∀(e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
        (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j),h.val.1=h'.val.1 →
      ‖sourceHistoryPairMean w j hj (fun l _=>B l) (fun l _=>V l) P e h h'-
        sourceCorePairMean w j hj B V P e h h'‖ ≤
        Real.exp (K*L^2-(1/4:ℝ)*Real.exp (α*L)) := by
  obtain ⟨K,hK,h⟩ := exists_eventually_sourcePair_support_removal k hα hαβ hρ hγ hc₀ hc hBD
  refine ⟨K,hK,?_⟩
  filter_upwards [h] with L hL
  intro d E δ hE hband s w j hj B V P hP e h h' hroot
  rw [sourceHistoryPairMean_eq_start w j hj (fun l _=>B l) (fun l _=>V l) hc P e h h' hroot,
    ←sourcePairEndKernel_fullProductMean_eq_coreAmplitude w j hj B V P e h h']
  exact hL d E δ hE hband s w j hj (fun l _=>B l) (fun l _=>V l) P hP e h h'

end Ostmann.Characters.DiagonalEstimate

end

end OAI
