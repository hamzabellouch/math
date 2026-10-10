import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSourceScalesPair

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSourceScales
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate Template
open DiagonalEstimate HigherBiasSourceWord Template.OneSidedPhase InitialCharacterScale
attribute [local instance] Classical.propDecidable

theorem changed_actualCode_sourceEdge_scales
    {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) (hα : 0<α) (hγ : 0<γ) (hL : 0<L)
    (hband : ∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L)
    (j : ℕ) (hj : j<k)
    (σ τ : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (hσ : ∀i,IsCopiedBulk w.configuration (wordSize k L) j (σ i) ↔
      IsCopiedBulk w.configuration (wordSize k L) j i)
    (hτ : ∀i,IsCopiedBulk w.configuration (wordSize k L) j (τ i) ↔
      IsCopiedBulk w.configuration (wordSize k L) j i)
    (hcode : ¬∀i,actualCopiedCode w.configuration (wordSize k L) j (σ i)=
      actualCopiedCode w.configuration (wordSize k L) j (τ i)) :
    ∃P R : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)),
      ∃positive : Bool, ∃n : Fin (scaleCount β γ),
      P≠R ∧
      survivingDifferenceGraph k j hj (sourceWidth w.configuration (wordSize k L))
        (copiedSurvivingPermutation k j (sourceWidth w.configuration (wordSize k L)) σ)
        (copiedSurvivingPermutation k j (sourceWidth w.configuration (wordSize k L)) τ) R P=
          (if positive then 2 else -2) ∧
      survivingDifferenceGraph k j hj (sourceWidth w.configuration (wordSize k L))
        (copiedSurvivingPermutation k j (sourceWidth w.configuration (wordSize k L)) σ)
        (copiedSurvivingPermutation k j (sourceWidth w.configuration (wordSize k L)) τ) P R=0 ∧
      0<n.val ∧ 0<lowerExponent α γ ∧ lowerExponent α γ ≤ shortExponent γ n.val ∧
      shortExponent γ n.val<longExponent γ n.val ∧
      (∀p∈sourceSurvivorShells w j R,
        Real.exp (lowerExponent α γ*L)≤Real.log p.val ∧
          Real.log p.val≤Real.exp (shortExponent γ n.val*L)) ∧
      (∀p∈sourceSurvivorShells w j P,
        Real.exp ((longExponent γ n.val+scaleStep γ)*L)≤Real.log p.val ∧
          Real.log p.val≤Real.exp (β*L)) ∧
      (∀p∈sourceSurvivorShells w j P,∀q∈sourceSurvivorShells w j R,p.val.Coprime q.val) := by
  obtain ⟨P,R,positive,hne,hforward,hreverse,hshape⟩ :=
    changed_actualCode_sourceEdge w.configuration (wordSize k L) j hj σ τ hσ hτ hcode
  obtain ⟨n,hn,hαp,hαβ,hβγ,hshort,hlong⟩ :=
    source_edge_grid w hα hγ hL hband j hj.le P R hshape
  exact ⟨P,R,positive,n,hne,hforward,hreverse,hn,hαp,hαβ,hβγ,hshort,hlong,
    source_edge_coprime w hγ hL j hj.le P R hshape⟩

end Ostmann.Characters.TemplateOneSidedSourceScales

end

end OAI
