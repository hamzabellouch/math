import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateUnitMatching
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSurvivorNorm

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem unit_matched_root_energy_le (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q U : ℕ}
    (E : (schedule k j).Constituent width→Finset (PrimeUpTo Q)) (hE : ∀i,0<primeShellMass (E i))
    (ζ : PrimeUnitData (schedule k j) width Q) (hζ : ∀i p,‖ζ i p‖=1)
    (χ : PrimeCharacterData (schedule k j) width Q) (hχ : ∀i p,p∈E i→χ i p≠1)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask : (l:ℕ)→ℤ→State k l→Prop) (X Δ W : ℝ)
    (S : List Bool→Finset ℤ) (path : List Bool)
    (hU : ∀i p,p∈E i→U<p.val)
    (hS : ∀path f,f∈S path→f≠0 ∧ f.natAbs≤U)
    (y : OutsideConstituent (schedule k j) j width→PrimeUpTo Q)
    (hy : (outsidePrimePrior (schedule k j) j width E hE).mass y≠0)
    (P : ℕ+) (A : Finset (Equiv.Perm (CopiedConstituent (schedule k j) j width))) (T D H : ℝ)
    (hrange : ∀f,(copiedPrimePrior (schedule k j) j width E hE).mass f≠0→
      ∀z:SupportedHistory S j path,
      RetainedRow.term k j B V extra mask X Δ W P
        (copiedSampleState (schedule k j) j width f) (outsideSampleState (schedule k j) j width y)
        z.val (unitRetainedPhase k j hj width ζ χ a f y P z.val.1 z.val.2)≠0→
      Real.exp (T+D-H)≤((∏i,(f i).val:ℕ):ℝ)) :
    (matchedRootContribution (fun i=>E (copiedConstituentOld (schedule k j) j width i))
      (fun _i=>hE _) A (unitRootRow k j hj width ζ χ a B V extra mask X Δ W S path y P)).re ≤
      (A.card:ℝ)*(copiedNormalization (fun i=>E (copiedConstituentOld (schedule k j) j width i))*
        Real.exp (-T-D+H))*
        (copiedPrimePrior (schedule k j) j width E hE).mean (fun f=>
          ∑z:SupportedHistory S j path,‖retainedHistoryWeight k B V extra mask X Δ W j z.val.1
            (sourceState k j (P:ℤ) (copiedSampleState (schedule k j) j width f)
              (outsideSampleState (schedule k j) j width y)) z.val.2‖^2) := by
  have hb := matchedRootContribution_le_normalized_energy
    (fun i=>E (copiedConstituentOld (schedule k j) j width i)) (fun i=>hE _) A
    (unitRootRow k j hj width ζ χ a B V extra mask X Δ W S path y P) T D H (by
      intro f hf s hs
      obtain ⟨z,hz,ht⟩ := historyRootSum_nonzero_term k j S path B V extra mask X Δ W s.val
        (sourceState k j (P:ℤ) (copiedSampleState (schedule k j) j width f)
          (outsideSampleState (schedule k j) j width y)) _ hs
      exact hrange f hf z ht)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
  · unfold FinitePrior.mean
    apply Finset.sum_le_sum
    intro f hf
    by_cases hm : (copiedPrimePrior (schedule k j) j width E hE).mass f=0
    · change _≤(copiedPrimePrior (schedule k j) j width E hE).mass f*_
      change (copiedPrimePrior (schedule k j) j width E hE).mass f*_≤_
      simp only [hm,zero_mul,le_refl]
    apply mul_le_mul_of_nonneg_left
    · exact historyRootSum_total_norm_sq_le k j S path B V extra mask X Δ W
        (sourceState k j (P:ℤ) (copiedSampleState (schedule k j) j width f)
          (outsideSampleState (schedule k j) j width y))
        (fun _ z=>unitRetainedPhase k j hj width ζ χ a f y P z.val.1 z.val.2)
        (fun _ z=>norm_unitRetainedPhase_le_of_mass k j hj width E hE ζ hζ χ hχ a hU
          f y hm hy S hS path z P)
    · exact FinitePrior.mass_nonneg _ f
  · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (copiedNormalization_nonneg _ (fun i=>hE _))
      (Real.exp_pos _).le)

end Ostmann.Characters.DiagonalEstimate

end

end OAI
