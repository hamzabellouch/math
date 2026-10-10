import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceEnergy

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale Filter
attribute [local instance] Classical.propDecidable

def sourceDiagonalOverhead (k : ℕ) (c c₀ : ℝ) : ℝ :=
  (2^k:ℕ)*|Real.log c₀|+(sourceCopiedWidth k c+sourceAtomWidth k c)+sourceNonbulkLogCost k

theorem eventually_sourcePreservingAverage_le (d : Decomposition)
    {δ α β ρ γ c₀ c : ℝ} (hα : 0<α) (hαβ : α<β)
    (hρ : 0<ρ) (hγ : 0<γ) (hc₀ : 0<c₀) (hc : 0<c) :
    ∀ᶠ k : ℕ in atTop,∀BD : ℝ,0<BD → ∀ᶠL : ℝ in atTop,
      ∀E : Finset ℕ,(∀p∈E,p.Prime) →
      (∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀j : ℕ,∀hj : j<k,∀B V : (l:ℕ) → State k (l+1) → ℤ,
      sourcePreservingAverage w j hj B V ≤
        Real.exp (-gapSchedule BD k L (j+1)+
          (2:ℝ)^j*(wordSize k L:ℝ)*(Real.log (depthScale k)+(|Real.log ρ|+2)+Real.log 2)+
          (β+1)*(2:ℝ)^j*L+(wordSize k L:ℝ)+sourceDiagonalOverhead k c c₀) := by
  filter_upwards [eventually_fixedConfiguration_code_factor d hα hαβ hρ hγ hc₀ hc] with k hk
  intro BD hBD
  have hall := Filter.eventually_all.mpr (fun i : Fin k=>
    eventually_sourceMatchingAverage_le (δ:=δ) (c₀:=c₀) d k i.val i.isLt hα hαβ hρ hγ hc hBD)
  filter_upwards [hk BD,hall] with L hfactor henergy
  intro E hE hband s w j hj B V
  have hmain := henergy ⟨j,hj⟩ E hE hband s w B V
    (codePreservingMatchings w.configuration (wordSize k L) j)
  have hnum := hfactor E hE s w j hj.le (gapSchedule BD k L (j+1))
    (sourceCopiedWidth k c+sourceAtomWidth k c)
  apply hmain.trans
  simpa only [sourceDiagonalOverhead,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,add_assoc] using hnum

end Ostmann.Characters.DiagonalEstimate

end

end OAI
