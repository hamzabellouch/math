import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceReindexBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateHistory

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template

theorem reconstructedPivot_positive_frequency_reindex (k j : ℕ) (x : State k (j+1))
    (v w : ℤ) (R : Finset ℕ) (hR : ∀ P ∈ R, 0 < P) (T : Finset ℤ) (F : ℤ → ℂ)
    (hcut : ∀ P ∈ R, ∀ s : ℤ,
      v*copiedProduct k j false x-w*copiedProduct k j true x ≠ 0 →
      v*copiedProduct k j false x-w*copiedProduct k j true x=s*(P:ℤ) →
      F (P:ℤ) ≠ 0 → s ∈ T) :
    (∑ P ∈ R, if (P:ℤ) ∣ v*copiedProduct k j false x-w*copiedProduct k j true x ∧
      v*copiedProduct k j false x-w*copiedProduct k j true x ≠ 0 then F (P:ℤ) else 0)=
      ∑ s ∈ T, if s ≠ 0 ∧ 0 < reconstructedPivot k j x s v w ∧
        (reconstructedPivot k j x s v w).toNat ∈ R ∧
        s*reconstructedPivot k j x s v w=
          v*copiedProduct k j false x-w*copiedProduct k j true x
        then F (reconstructedPivot k j x s v w) else 0 := by
  classical
  refine (positive_pivot_frequency_reindex
    (v*copiedProduct k j false x-w*copiedProduct k j true x) R hR T F hcut).trans ?_
  apply Finset.sum_congr rfl
  intro s hs
  unfold reconstructedPivot
  split_ifs <;> rfl

theorem reconstructedPivot_frequency_reindex_with_diagonal (k j : ℕ) (x : State k (j+1))
    (v w : ℤ) (R : Finset ℕ) (hR : ∀ P ∈ R, 0 < P) (T : Finset ℤ) (F : ℤ → ℂ)
    (hcut : ∀ P ∈ R, ∀ s : ℤ,
      v*copiedProduct k j false x-w*copiedProduct k j true x ≠ 0 →
      v*copiedProduct k j false x-w*copiedProduct k j true x=s*(P:ℤ) →
      F (P:ℤ) ≠ 0 → s ∈ T) :
    (∑ P ∈ R, if (P:ℤ) ∣ v*copiedProduct k j false x-w*copiedProduct k j true x
      then F (P:ℤ) else 0)=
      (if v*copiedProduct k j false x=w*copiedProduct k j true x
        then ∑ P ∈ R,F (P:ℤ) else 0)+
      ∑ s ∈ T, if s ≠ 0 ∧ 0 < reconstructedPivot k j x s v w ∧
        (reconstructedPivot k j x s v w).toNat ∈ R ∧
        s*reconstructedPivot k j x s v w=
          v*copiedProduct k j false x-w*copiedProduct k j true x
        then F (reconstructedPivot k j x s v w) else 0 := by
  classical
  refine (positive_pivot_frequency_reindex_with_diagonal
    (v*copiedProduct k j false x-w*copiedProduct k j true x) R hR T F hcut).trans ?_
  apply congrArg₂ (· + ·)
  · by_cases hd : v*copiedProduct k j false x=w*copiedProduct k j true x
    · simp only [sub_eq_zero,hd,ite_true]
    · simp only [sub_eq_zero,hd,ite_false]
  · apply Finset.sum_congr rfl
    intro s hs
    unfold reconstructedPivot
    split_ifs <;> rfl

theorem reconstructedPivot_interval_frequency_reindex (k j B : ℕ) (x : State k (j+1))
    (v w V : ℤ) (F : ℤ → ℂ)
    (hcut : ∀ P ∈ Finset.Icc 1 B, ∀ s : ℤ,
      v*copiedProduct k j false x-w*copiedProduct k j true x ≠ 0 →
      v*copiedProduct k j false x-w*copiedProduct k j true x=s*(P:ℤ) →
      F (P:ℤ) ≠ 0 → |s| ≤ V) :
    (∑ P ∈ Finset.Icc 1 B, if (P:ℤ) ∣ v*copiedProduct k j false x-w*copiedProduct k j true x ∧
      v*copiedProduct k j false x-w*copiedProduct k j true x ≠ 0 then F (P:ℤ) else 0)=
      ∑ s ∈ Finset.Icc (-V) V, if s ≠ 0 ∧ 0 < reconstructedPivot k j x s v w ∧
        (reconstructedPivot k j x s v w).toNat ∈ Finset.Icc 1 B ∧
        s*reconstructedPivot k j x s v w=
          v*copiedProduct k j false x-w*copiedProduct k j true x
        then F (reconstructedPivot k j x s v w) else 0 := by
  apply reconstructedPivot_positive_frequency_reindex k j x v w _
    (fun P hP => (Finset.mem_Icc.mp hP).1) _ F
  intro P hP s hN hs hf
  exact Finset.mem_Icc.mpr (abs_le.mp (hcut P hP s hN hs hf))

end Ostmann.Characters.Template

end

end OAI
