import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateMatchingPairs
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportTags
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryRootNorm

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Construction Template HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

def historyRootIndex (j : ℕ) (S : List Bool→Finset ℤ) (path : List Bool)
    (z : SupportedHistory S j path) : ↥(S path) :=
  ⟨z.val.1,mem_labels_range S z.property (root_mem_labels j path z.val.1 z.val.2)⟩

theorem retained_diagonal_eq_root_pairs {α : Type*} [Fintype α]
    (k j : ℕ) (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask : (l:ℕ)→ℤ→State k l→Prop) (X Δ W : ℝ)
    (μ : FinitePrior α) (h : α → CopiedState k j) (y : OutsideState k j)
    (S : List Bool→Finset ℤ) (path : List Bool) (P : ℕ+)
    (phase : α→SupportedHistory S j path→ℂ) :
    historyRowDiagonal k j μ h y S path mask X Δ W P
      (fun x z=>RetainedRow.guardPhase k j B V extra P (h x) y z.val (phase x z)) =
      ∑x,∑x',((μ.mass x*μ.mass x':ℝ):ℂ)*
        (if (∏i,h x' i)=(∏i,h x i) then
          ∑s:↥(S path),
            historyRootSum k j S path B V extra mask X Δ W s.val
              (sourceState k j (P:ℤ) (h x) y) (phase x)*
            conj (historyRootSum k j S path B V extra mask X Δ W s.val
              (sourceState k j (P:ℤ) (h x') y) (phase x'))
        else 0) := by
  have he := refinedRowDiagonal_eq_root_pairs μ (historyRootIndex j S path)
    (fun x=>∏i,h x i) (fun x z=>historyExactTag k j (h x) z.val.1)
    (fun x z=>RetainedRow.term k j B V extra mask X Δ W P (h x) y z.val (phase x z)) (by
      intro x x' z z' hx hx' hz hz'
      have hh := RetainedRow.term_exactTag_iff k j B V extra mask X Δ W P (h x') (h x) y
        z'.val z.val (phase x' z') (phase x z) hz' hz
      simpa only [historyRootIndex,Subtype.mk.injEq] using hh)
  have hleft : historyRowDiagonal k j μ h y S path mask X Δ W P
      (fun x z=>RetainedRow.guardPhase k j B V extra P (h x) y z.val (phase x z)) =
      refinedRowDiagonal (fun a:α×SupportedHistory S j path=>μ.mass a.1)
        (fun a=>historyExactTag k j (h a.1) a.2.val.1)
        (fun a=>RetainedRow.term k j B V extra mask X Δ W P (h a.1) y a.2.val (phase a.1 a.2)) := by
    unfold historyRowDiagonal
    congr 1
    funext a
    exact (RetainedRow.term_eq k j B V extra mask X Δ W P (h a.1) y a.2.val (phase a.1 a.2)).symm
  rw [hleft,he]
  simp only [historyRootSum,historyRootIndex,Subtype.ext_iff,RetainedRow.term]

theorem historyRootSum_nonzero_term (k j : ℕ) (S : List Bool→Finset ℤ) (path : List Bool)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask : (l:ℕ)→ℤ→State k l→Prop) (X Δ W : ℝ) (s : ℤ)
    (x : State k j) (phase : SupportedHistory S j path→ℂ)
    (hn : historyRootSum k j S path B V extra mask X Δ W s x phase≠0) :
    ∃z:SupportedHistory S j path,z.val.1=s ∧
      retainedHistoryWeight k B V extra mask X Δ W j z.val.1 x z.val.2*phase z≠0 := by
  by_contra hall
  push Not at hall
  apply hn
  unfold historyRootSum
  apply Finset.sum_eq_zero
  intro z hz
  by_cases he : z.val.1=s
  · rw [ite_eq_left he,hall z he]
  · exact ite_eq_right he

end Ostmann.Characters.DiagonalEstimate

end

end OAI
