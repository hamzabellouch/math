import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateEnergy
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryRootNorm

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Ostmann.Preliminaries Ostmann.Construction Template HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem harmonic_matching_vector_norm_sum_le
    {I κ : Type*} [Fintype I] [DecidableEq I] [Fintype κ] {N : ℕ}
    (E : I → Finset (PrimeUpTo N)) (hE : ∀i,0<primeShellMass (E i))
    (A : Finset (Equiv.Perm I)) (F : (I→PrimeUpTo N)→κ→ℂ) (T Δ W : ℝ)
    (hrange : ∀f,(productPrior (fun i => primeShellPrior (E i) (hE i))).mass f≠0 →
      ∀s,F f s≠0 → Real.exp (T+Δ-W)≤((∏i,(f i).val : ℕ):ℝ)) :
    let μ := productPrior (fun i => primeShellPrior (E i) (hE i))
    (∑s,∑e∈A,∑f,μ.mass f*μ.mass (f ∘ e)*‖F f s‖*‖F (f ∘ e) s‖) ≤
      (A.card:ℝ)*(copiedNormalization E*Real.exp (-T-Δ+W))*
        μ.mean (fun f => ∑s,‖F f s‖^2) := by
  dsimp only
  calc
    _ ≤ ∑s,(A.card:ℝ)*(copiedNormalization E*Real.exp (-T-Δ+W))*
        (productPrior (fun i => primeShellPrior (E i) (hE i))).mean (fun f => ‖F f s‖^2) :=
      Finset.sum_le_sum fun s _ => harmonic_matching_family_norm_sum_le E hE A (fun f=>F f s)
        T Δ W (fun f hf hfs=>hrange f hf s hfs)
    _ = _ := by
      rw [←Finset.mul_sum]
      congr 1
      simp only [FinitePrior.mean,Finset.mul_sum]
      exact Finset.sum_comm

theorem historyRootSum_nonzero_history (k j:ℕ) (S:List Bool→Finset ℤ) (path:List Bool)
    (B V:(l:ℕ)→State k (l+1)→ℤ)
    (extra:(l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask:(l:ℕ)→ℤ→State k l→Prop) (X Δ W:ℝ) (s:ℤ) (x:State k j)
    (phase:SupportedHistory S j path→ℂ)
    (hn : historyRootSum k j S path B V extra mask X Δ W s x phase≠0) :
    ∃h:SupportedHistory S j path,h.val.1=s ∧
      retainedHistoryWeight k B V extra mask X Δ W j h.val.1 x h.val.2≠0 := by
  by_contra hall
  push Not at hall
  apply hn
  unfold historyRootSum
  apply Finset.sum_eq_zero
  intro h hh
  by_cases he : h.val.1=s
  · rw [ite_eq_left he,hall h he,zero_mul]
  · exact ite_eq_right he

theorem harmonic_matching_history_root_sum_le
    {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}
    (E : I → Finset (PrimeUpTo N)) (hE : ∀i,0<primeShellMass (E i))
    (A : Finset (Equiv.Perm I)) (k j:ℕ) (S:List Bool→Finset ℤ) (path:List Bool)
    (B V:(l:ℕ)→State k (l+1)→ℤ)
    (extra:(l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask:(l:ℕ)→ℤ→State k l→Prop) (X Δ W T D H:ℝ)
    (x:(I→PrimeUpTo N)→State k j)
    (phase:(I→PrimeUpTo N)→ℤ→SupportedHistory S j path→ℂ)
    (hphase : ∀f,(productPrior (fun i => primeShellPrior (E i) (hE i))).mass f≠0 →
      ∀s h,‖phase f s h‖≤1)
    (hrange : ∀f,(productPrior (fun i => primeShellPrior (E i) (hE i))).mass f≠0 →
      ∀h:SupportedHistory S j path,
      retainedHistoryWeight k B V extra mask X Δ W j h.val.1 (x f) h.val.2≠0 →
      Real.exp (T+D-H)≤((∏i,(f i).val : ℕ):ℝ)) :
    let μ := productPrior (fun i => primeShellPrior (E i) (hE i))
    let F := fun f s=>historyRootSum k j S path B V extra mask X Δ W s (x f) (phase f s)
    (∑s:↥(S path),∑e∈A,∑f,μ.mass f*μ.mass (f ∘ e)*‖F f s.val‖*‖F (f ∘ e) s.val‖) ≤
      (A.card:ℝ)*(copiedNormalization E*Real.exp (-T-D+H))*
        μ.mean (fun f => ∑h:SupportedHistory S j path,
          ‖retainedHistoryWeight k B V extra mask X Δ W j h.val.1 (x f) h.val.2‖^2) := by
  dsimp only
  apply (harmonic_matching_vector_norm_sum_le E hE A
    (fun f (s:↥(S path)) => historyRootSum k j S path B V extra mask X Δ W s.val (x f) (phase f s.val))
    T D H (by
      intro f hf s hs
      obtain ⟨h,hr,hh⟩ := historyRootSum_nonzero_history k j S path B V extra mask X Δ W s.val (x f)
        (phase f s.val) hs
      exact hrange f hf h hh)).trans
  apply mul_le_mul_of_nonneg_left
  · unfold FinitePrior.mean
    apply Finset.sum_le_sum
    intro f hf
    by_cases hm : (productPrior (fun i => primeShellPrior (E i) (hE i))).mass f=0
    · simp only [hm,zero_mul,le_refl]
    apply mul_le_mul_of_nonneg_left
    · exact historyRootSum_total_norm_sq_le k j S path B V extra mask X Δ W (x f) (phase f)
        (hphase f hm)
    · exact FinitePrior.mass_nonneg _ f
  · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (copiedNormalization_nonneg E hE)
      (Real.exp_pos _).le)

end Ostmann.Characters.DiagonalEstimate

end

end OAI
