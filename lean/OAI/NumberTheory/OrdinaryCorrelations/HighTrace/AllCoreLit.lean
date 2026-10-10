import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeSplit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.NumericalLine
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LocalUnlitCount
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RepeatedUnlitTotalEqFixed
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceWitnessErrorBelowTrace
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UnlitPolynomialBound

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical Filter
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

def AllCoreLit (w : ClosedLine h ℓ) (a : S.FixedResidues w) : Prop :=
  ∀ p : S.FixedIndex w, S.IsCore p.val → ∀ i,
    (p.val:ℕ) ∣ w.label i → a p+(w.offset i.castSucc : ZMod (p.val:ℕ))=0

lemma kernel_zero_of_core_unlit (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (r : S.Residues) (hc : ¬AllCoreLit w ((S.binarySplit w r).1)) :
    S.chronologicalKernel w cut r=0 := by
  unfold AllCoreLit at hc
  push Not at hc
  obtain ⟨p,hp,i,hi,ha⟩ := hc
  have hpf : S.primeFactor w p.val (r p.val)=0 := by
    apply prod_eq_zero (mem_univ i)
    simp only [occurrenceFactor,hi,hp,ite_true]
    have he : r p.val+(w.offset i.castSucc : ZMod (p.val:ℕ)) ≠ 0 := ha
    simp [activity,he]
  rw [chronologicalKernel_eq,kernel,prod_eq_zero (mem_univ p.val) hpf,mul_zero]

lemma allowedIndicator_zero_of_fixed_forbidden (w : ClosedLine h ℓ) (r : S.Residues)
    (hf : ¬NoFixedForbidden w D L ((S.binarySplit w r).1)) :
    allowedIndicator w D L r=0 := by
  unfold NoFixedForbidden at hf
  push Not at hf
  obtain ⟨s,hs,hfix⟩ := hf
  have hh : s.fullCylinder.Holds r := by
    rw [s.fullCylinder_holds]
    intro p
    by_cases hp : S.IsFixed w p
    · exact hs ⟨p,hp⟩
    · exact s.spec.test_vacuous p (fun hm => hp (hfix p hm)) s.vertex (r p)
  exact ite_eq_right (fun hg => hg s hh)

namespace NumericalLine

def geometricErrorSum {B τ T C₀ : ℝ} (D : (sourceSystem B).DivisorFamily B τ C₀)
    {h ℓ : ℕ} (hh : 0 < h) (K₀ : ℝ) (cut : (sourceSystem B).Cutoffs T) : ℝ :=
  ∑ w : NumericalLine D h ℓ, avg (fun r : (sourceSystem B).Residues =>
    if AllCoreLit w.line ((sourceSystem B).binarySplit w.line r).1 ∧
      NoFixedForbidden w.line D (pathLength B) ((sourceSystem B).binarySplit w.line r).1 ∧
      repeatedUnlitTotal w.line r < listCutoff B ∧
      ¬sourceRetained hh K₀ w ((sourceSystem B).binarySplit w.line r).1 then
        |(sourceSystem B).chronologicalKernel w.line cut r*allowedIndicator w.line D (pathLength B) r|
    else 0)

lemma discarded_le_unlit_add_geometric {B τ T C₀ : ℝ}
    (D : (sourceSystem B).DivisorFamily B τ C₀) {h ℓ : ℕ}
    (hh : 0 < h) (K₀ : ℝ) (cut : (sourceSystem B).Cutoffs T) :
    discardedTraceSum D h ℓ (pathLength B) cut (sourceRetained hh K₀) ≤
      unlitTailSum D h ℓ (pathLength B) cut (listCutoff B)+geometricErrorSum D (ℓ := ℓ) hh K₀ cut := by
  unfold discardedTraceSum unlitTailSum geometricErrorSum
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro w hw
  rw [←OrdinaryCorrelations.SourceCylinder.avg_add']
  apply avg_mono
  intro r
  by_cases hg : sourceRetained hh K₀ w ((sourceSystem B).binarySplit w.line r).1
  · rw [ite_eq_left hg]
    have he : ¬(AllCoreLit w.line ((sourceSystem B).binarySplit w.line r).1 ∧
      NoFixedForbidden w.line D (pathLength B) ((sourceSystem B).binarySplit w.line r).1 ∧
      repeatedUnlitTotal w.line r < listCutoff B ∧
      ¬sourceRetained hh K₀ w ((sourceSystem B).binarySplit w.line r).1) := fun he => he.2.2.2 hg
    rw [ite_eq_right he,add_zero]
    split_ifs <;> positivity
  · rw [ite_eq_right hg]
    by_cases hc : AllCoreLit w.line ((sourceSystem B).binarySplit w.line r).1
    · by_cases hf : NoFixedForbidden w.line D (pathLength B) ((sourceSystem B).binarySplit w.line r).1
      · by_cases ht : listCutoff B ≤ repeatedUnlitTotal w.line r
        · simp only [hc,hf,ht,not_lt_of_ge ht,hg,not_false_eq_true,true_and,
            false_and,ite_false,ite_true,add_zero,le_refl]
        · have hlt := Nat.lt_of_not_ge ht
          simp only [hc,hf,ht,hlt,hg,not_false_eq_true,and_self,ite_true,ite_false,zero_add,le_refl]
      · rw [allowedIndicator_zero_of_fixed_forbidden w.line r hf,mul_zero,abs_zero]
        split_ifs <;> norm_num
    · rw [kernel_zero_of_core_unlit w.line cut r hc,zero_mul,abs_zero]
      split_ifs <;> norm_num

theorem source_full_trace_with_geometry (h : ℕ) (hh : 0 < h) (τ T C₀ K₀ : ℝ)
    (hτ : 1 ≤ τ) (hτ2 : τ < 2) (hC₀ : 0 ≤ C₀) (hK₀ : 0 ≤ K₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      fullTraceSum D h (sourceLength B) (pathLength B) cut ≤
        B^(-(1+eta)*(sourceLength B:ℝ))+Real.exp (-B^(1+epsilon/2))+
          geometricErrorSum D (ℓ := sourceLength B) hh K₀ cut := by
  filter_upwards [source_full_trace_with_discarded h hh τ T C₀ K₀ hτ hτ2 hC₀ hK₀,
    source_unlit_tail_small h τ T C₀ hC₀] with B ht hu
  intro D cut
  calc
    _ ≤ _ := ht D cut
    _ ≤ B^(-(1+eta)*(sourceLength B:ℝ))+
        (unlitTailSum D h (sourceLength B) (pathLength B) cut (listCutoff B)+geometricErrorSum D (ℓ := sourceLength B) hh K₀ cut) :=
      add_le_add le_rfl (discarded_le_unlit_add_geometric D (ℓ := sourceLength B) hh K₀ cut)
    _ ≤ _ := by linarith [hu D cut]

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
