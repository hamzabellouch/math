import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateExternal
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateUnitEnergy
import OAI.NumberTheory.Ostmann.Characters.TemplateConstituentNormFixed

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HistoryFrequencyLabels HistoryFrequencyBudget Filter
attribute [local instance] Classical.propDecidable

section
variable (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width→Finset (PrimeUpTo Q)) (hE : ∀i,0<primeShellMass (E i))
    (ζ : PrimeUnitData (schedule k j) width Q) (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask : (l:ℕ)→ℤ→State k l→Prop) (X Δ W : ℝ)
    (S : List Bool→Finset ℤ) (R : Finset ℕ+)

def unitMatchingAverage (A : Finset (Equiv.Perm (CopiedConstituent (schedule k j) j width))) : ℝ :=
  (outsidePrimePrior (schedule k j) j width E hE).mean (fun y=>∑P∈R,
    (matchedRootContribution (fun i=>E (copiedConstituentOld (schedule k j) j width i))
      (fun _=>hE _) A (unitRootRow k j hj width ζ χ a B V extra mask X Δ W S [] y P)).re)

theorem unitDiagonal_matching_partition
    (A : Finset (Equiv.Perm (CopiedConstituent (schedule k j) j width))) :
    unitDiagonal k j hj width E hE ζ χ a B V extra mask X Δ W S R =
      unitMatchingAverage k j hj width E hE ζ χ a B V extra mask X Δ W S R A+
      unitMatchingAverage k j hj width E hE ζ χ a B V extra mask X Δ W S R (Finset.univ\A) := by
  rw [unitDiagonal_eq_matching]
  simp only [matchedRootContribution_partition _ _ A,Complex.add_re,Finset.sum_add_distrib,
    unitMatchingAverage,FinitePrior.mean,mul_add,Finset.sum_add_distrib]

end

theorem eventually_unitMatchingAverage_le (j K : ℕ) (hjK : j≤K)
    {z b α β c δ : ℝ} (hz : 0<z) (hb : 0<b) (hα : 0<α) (hβ : 0≤β)
    (hc : 0≤c) (hδ : 0<δ) (W : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀Q U : ℕ,∀E0 : Finset (PrimeUpTo Q),∀_hE0 : 0<primeShellMass E0,
      Real.exp (-c*L)≤primeShellMass E0→
      (∀p∈E0,Real.exp (α*L)≤Real.log p.val)→
      (∀p∈E0,Real.log p.val≤Real.exp (β*L))→
      ∀k : ℕ,∀hj : j<k,∀width : Role→ℕ,∀hw : 0<width .word,
      ∀E : (schedule k j).Constituent width→Finset (PrimeUpTo Q),∀hE : ∀i,0<primeShellMass (E i),
      (∀w,E (chosenPrimeIndex k j width hw w)=E0)→
      ∀ζ : PrimeUnitData (schedule k j) width Q,(∀i p,‖ζ i p‖=1)→
      ∀χ : PrimeCharacterData (schedule k j) width Q,(∀i p,p∈E i→χ i p≠1)→
      ∀a : PrimeTranslationData (schedule k j) width Q,
      ∀B V : (l:ℕ)→State k (l+1)→ℤ,
      ∀extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop,
      ∀mask : (l:ℕ)→ℤ→State k l→Prop,∀X : ℝ,0<X→
      (∀i p,p∈E i→U<p.val)→
      (∀path f,f∈ranges b (⌊z*L⌋₊:ℝ) j path→f≠0 ∧ f.natAbs≤U)→
      ∀R : Finset ℕ+,∀A : Finset (Equiv.Perm (CopiedConstituent (schedule k j) j width)),
      ∀T D H Vp : ℝ,(∀P∈R,(P:ℝ)≤Real.exp (T+Vp))→
      (∀P∈R,∀y,(outsidePrimePrior (schedule k j) j width E hE).mass y≠0→
        ∀f,(copiedPrimePrior (schedule k j) j width E hE).mass f≠0→
        ∀q:SupportedHistory (ranges b (⌊z*L⌋₊:ℝ) j) j [],
        RetainedRow.term k j B V extra mask X (b*(⌊z*L⌋₊:ℝ)) W P
          (copiedSampleState (schedule k j) j width f) (outsideSampleState (schedule k j) j width y)
          q.val (unitRetainedPhase k j hj width ζ χ a f y P q.val.1 q.val.2)≠0→
        Real.exp (T+D-H)≤((∏i,(f i).val:ℕ):ℝ))→
      unitMatchingAverage k j hj width E hE ζ χ a B V extra mask X (b*(⌊z*L⌋₊:ℝ)) W
        (ranges b (⌊z*L⌋₊:ℝ) j) R A ≤
      ((A.card:ℝ)*copiedNormalization (fun i=>E (copiedConstituentOld (schedule k j) j width i)))*
        Real.exp (-D+H+Vp)*Real.exp ((β+c+1)*(2:ℝ)^j*L+δ*(⌊z*L⌋₊:ℝ)) := by
  filter_upwards [fixed_pivot_retained_square_sum_eventually j K hjK hz hb hα hβ hc hδ W] with L hL
  intro Q U E0 hE0 hmass hmin hmax k hj width hw E hE hchosen ζ hζ χ hχ a B V extra mask X hX
    hU hS R A T D H Vp hR hrange
  let C : ℝ := (A.card:ℝ)*copiedNormalization (fun i=>E (copiedConstituentOld (schedule k j) j width i))
  have hC : 0≤C := mul_nonneg (Nat.cast_nonneg _) (copiedNormalization_nonneg _ (fun _=>hE _))
  let M : ℝ := Real.exp ((β+c+1)*(2:ℝ)^j*L+δ*(⌊z*L⌋₊:ℝ))
  apply normalized_external_sum_le _ R _ C T D H Vp M hC (Real.exp_pos _).le hR
  intro P hP
  have hpoint (y) (hy : (outsidePrimePrior (schedule k j) j width E hE).mass y≠0) :=
    unit_matched_root_energy_le k j hj width E hE ζ hζ χ hχ a B V extra mask X
      (b*(⌊z*L⌋₊:ℝ)) W (ranges b (⌊z*L⌋₊:ℝ) j) [] hU hS y hy P A T D H
      (hrange P hP y hy)
  have hnorm := hL Q E0 hE0 hmass hmin hmax k hj width hw E hE hchosen B V extra mask X hX (P:ℤ)
  have hfactor : 0≤C*Real.exp (-T-D+H) := mul_nonneg hC (Real.exp_pos _).le
  calc
    _ ≤ (outsidePrimePrior (schedule k j) j width E hE).mean (fun y=>
        C*Real.exp (-T-D+H)*(copiedPrimePrior (schedule k j) j width E hE).mean (fun f=>
          ∑q:SupportedHistory (ranges b (⌊z*L⌋₊:ℝ) j) j [],
          ‖retainedHistoryWeight k B V extra mask X (b*(⌊z*L⌋₊:ℝ)) W j q.val.1
            (sourceState k j (P:ℤ) (copiedSampleState (schedule k j) j width f)
              (outsideSampleState (schedule k j) j width y)) q.val.2‖^2)) := by
      unfold FinitePrior.mean
      apply Finset.sum_le_sum
      intro y hy
      by_cases hmy : (outsidePrimePrior (schedule k j) j width E hE).mass y=0
      · simp only [hmy,zero_mul,le_refl]
      apply mul_le_mul_of_nonneg_left _ (FinitePrior.mass_nonneg _ _)
      simpa only [C,mul_assoc,FinitePrior.mean] using hpoint y hmy
    _ ≤ C*Real.exp (-T-D+H)*M := by
      have he : ∀g, (outsidePrimePrior (schedule k j) j width E hE).mean
          (fun y=>C*Real.exp (-T-D+H)*g y)=C*Real.exp (-T-D+H)*
          (outsidePrimePrior (schedule k j) j width E hE).mean g := by
        intro g
        simp only [FinitePrior.mean,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_left hnorm hfactor

end Ostmann.Characters.DiagonalEstimate

end

end OAI
