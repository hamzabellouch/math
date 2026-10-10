import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetSampled
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingActual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairWeight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTelescoping
open Template TemplateOneSidedCancellation TemplateOneSidedBudget Preliminaries
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem retained_pair_eq_indicator {ι : Type*} (k : ℕ)
    (B V : (j:ℕ)→State k (j+1)→ℤ)
    (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
    (mask : (j:ℕ)→ℤ→State k j→Prop) (X Δ W T Wc : ℝ)
    (j : ℕ) (s : Bool→ℤ) (x : Bool→(ι→ℤ)→State k j)
    (t : Bool→HistoryReconstruction.Tree j) (P : (ι→ℤ)→ℤ)
    (phase : (ι→ℤ)→ℂ) (a : ι→ℤ) :
    copiedWindowRatio T Wc (P a)*phase a*
      retainedHistoryWeight k B V extra mask X Δ W j (s false) (x false a) (t false)*
      conj (retainedHistoryWeight k B V extra mask X Δ W j (s true) (x true a) (t true)) =
    if ∀r,TransferSupport k B V extra j (s r) (x r a) (t r)
      then pairedHistoryMultiplier k mask X Δ W T Wc j s x t P phase a else 0 := by
  simp only [retainedHistoryWeight,pairedHistoryMultiplier,Bool.forall_bool]
  split_ifs <;> simp_all

theorem core_pair_eq_indicator {ι : Type*} (k : ℕ)
    (B V : (j:ℕ)→State k (j+1)→ℤ)
    (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
    (mask : (j:ℕ)→ℤ→State k j→Prop) (X Δ W T Wc : ℝ)
    (j : ℕ) (s : Bool→ℤ) (x : Bool→(ι→ℤ)→State k j)
    (t : Bool→HistoryReconstruction.Tree j) (P : (ι→ℤ)→ℤ)
    (phase : (ι→ℤ)→ℂ) (a : ι→ℤ) :
    copiedWindowRatio T Wc (P a)*phase a*
      coreHistoryWeight k B V extra mask X Δ W j (s false) (x false a) (t false)*
      conj (coreHistoryWeight k B V extra mask X Δ W j (s true) (x true a) (t true)) =
    if ∀r,TransferCoreSupport k B V extra j (s r) (x r a) (t r)
      then pairedHistoryMultiplier k mask X Δ W T Wc j s x t P phase a else 0 := by
  simp only [coreHistoryWeight,pairedHistoryMultiplier,Bool.forall_bool]
  split_ifs <;> simp_all

theorem core_pair_fixed_gate {ι : Type*} (k : ℕ)
    (B V : (j:ℕ)→State k (j+1)→ℤ)
    (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
    (mask : (j:ℕ)→ℤ→State k j→Prop) (X Δ W T Wc : ℝ)
    (j : ℕ) (s : Bool→ℤ) (x : Bool→(ι→ℤ)→State k j)
    (t : Bool→HistoryReconstruction.Tree j) (P : (ι→ℤ)→ℤ)
    (phase : (ι→ℤ)→ℂ) (a : ι→ℤ) (sourceMask fixedGate : Bool) :
    (if sourceMask=true ∧
        (∀r,TransferCoreSupport k B V extra j (s r) (x r a) (t r)) ∧ fixedGate=true
      then pairedHistoryMultiplier k mask X Δ W T Wc j s x t P phase a else 0) =
    if fixedGate then if sourceMask then
      copiedWindowRatio T Wc (P a)*phase a*
        coreHistoryWeight k B V extra mask X Δ W j (s false) (x false a) (t false)*
        conj (coreHistoryWeight k B V extra mask X Δ W j (s true) (x true a) (t true))
      else 0 else 0 := by
  rw [core_pair_eq_indicator]
  cases sourceMask <;> cases fixedGate <;> simp

theorem sampled_prime_transfer_iff {k Q : ℕ}
    (B V : (j:ℕ)→State k (j+1)→ℤ)
    (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
    (j : ℕ) (hj : j≤k) (s : ℤ) (width : Role→ℕ)
    (p : (schedule k j).Constituent width→PrimeUpTo Q)
    (t : HistoryReconstruction.Tree j)
    (hp : Pairwise (fun u v=>(p u).val.Coprime (p v).val)) :
    TransferSupport k B V extra j s (constituentSampleState (schedule k j) width p) t ↔
      SampledTransferSupport k (constituentSampleState (schedule k j) width p)
        B V extra j (SampleOrigins.root k j) s
        (constituentSampleState (schedule k j) width p) t := by
  exact transferSupport_iff_sampled B V extra j hj s _ t
    ((constituent_prime_support_iff (schedule k j) width p).mp hp).1

theorem retained_prime_pair_eq_sampled {k Q : ℕ}
    (B V : (j:ℕ)→State k (j+1)→ℤ)
    (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
    (mask : (j:ℕ)→ℤ→State k j→Prop) (X Δ W T Wc : ℝ)
    (j : ℕ) (hj : j≤k) (s : Bool→ℤ) (width : Role→ℕ)
    (p : (schedule k j).Constituent width→PrimeUpTo Q)
    (t : Bool→HistoryReconstruction.Tree j)
    (P : ((schedule k j).Constituent width→ℤ)→ℤ)
    (phase : ((schedule k j).Constituent width→ℤ)→ℂ)
    (hp : Pairwise (fun u v=>(p u).val.Coprime (p v).val)) :
    let a := fun i=>((p i).val:ℤ)
    copiedWindowRatio T Wc (P a)*phase a*
      retainedHistoryWeight k B V extra mask X Δ W j (s false)
        (constituentSampleState (schedule k j) width p) (t false)*
      conj (retainedHistoryWeight k B V extra mask X Δ W j (s true)
        (constituentSampleState (schedule k j) width p) (t true)) =
    if ∀r,SampledTransferSupport k (fun u=>∏b,a ⟨u,b⟩) B V extra j
      (SampleOrigins.root k j) (s r) (evalExpressions a (sampledExpressions k j width)) (t r)
    then pairedHistoryMultiplier k mask X Δ W T Wc j s
      (fun _ a=>evalExpressions a (sampledExpressions k j width)) t P phase a else 0 := by
  dsimp only
  rw [←sampledExpressions_prime_eval k j width p]
  rw [retained_pair_eq_indicator k B V extra mask X Δ W T Wc j s
    (fun _ a=>evalExpressions a (sampledExpressions k j width)) t P phase (fun i=>((p i).val:ℤ))]
  congr 1
  apply propext
  apply forall_congr'
  intro r
  have hstate : constituentSampleState (schedule k j) width p =
      fun u=>∏b : Fin (width ((schedule k j).role u)),((p ⟨u,b⟩).val:ℤ) :=
    (sampledExpressions_prime_eval k j width p).symm.trans (sampledExpressions_eval k j width _)
  simpa only [sampledExpressions_prime_eval,hstate] using
    sampled_prime_transfer_iff B V extra j hj (s r) width p (t r) hp

end Ostmann.Characters.TemplateOneSidedSupportTelescoping

end

end OAI
