import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSizeBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsBins
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsTargets

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction Preliminaries HigherBiasSourceRoleBounds
attribute [local instance] Classical.propDecidable

variable {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
  (bulk top E : Finset (PrimeUpTo Q)) (J : ℤ) (Δ : ℕ → ℝ) (logX c : ℝ)

theorem source_copied_atom_target (hc : 0 < c)
    (hlist : ∀ a, |((cfg.2 a).sum:ℝ)-configurationTarget logX J Δ cfg a| ≤ 6/c)
    (hlen : ∀ a, ((cfg.2 a).length:ℝ) ≤ 2*Real.exp (2*((1/10000:ℝ)*k)))
    (h : CopiedConstituent (schedule k j) j (sourceWidth cfg m) → PrimeUpTo Q)
    (hmem : ∀ a,h a ∈ scheduledPrimeShells k (sourceWidth cfg m)
      (configurationPrimeShells cfg m bulk top E) j (copiedConstituentOld _ _ _ a))
    (hbin : ∀ i : WordSlot k j,⌊Real.log (copiedSampleState (schedule k j) j
      (sourceWidth cfg m) h ⟨i.val,word_copied _ _ _ i.property.1 i.property.2⟩:ℝ)⌋=J)
    (i : ScheduledCopiedSlots k j) :
    |Real.log (copiedSampleState (schedule k j) j (sourceWidth cfg m) h i:ℝ)-
      sourceRoleCenter cfg J Δ ((schedule k j).role i.val)| ≤ sourceAtomWidth k c := by
  rcases i.property.2 with hw | ⟨l,hl,hp⟩ | ⟨b,ha⟩
  · have hh := Int.floor_eq_iff.mp (hbin ⟨i.val,i.property.1,hw⟩)
    rw [hw]
    change |Real.log (copiedSampleState _ _ _ h i:ℝ)-(J:ℝ)| ≤ _
    have h1 := sourceAtomWidth_ge_one k hc
    apply abs_le.mpr
    constructor <;> linarith
  · have hlk := (scheduled_role_index_lt k j i.val).1 l hp
    have hh := scheduled_pivot_atom_target cfg m j bulk top E J Δ logX c hc hlist hlen
      i.val ⟨l,hlk⟩ hp (fun a => h ⟨i,a⟩) (fun a => hmem ⟨i,a⟩)
    rw [hp]
    change |Real.log (((∏ a,((h ⟨i,a⟩).val:ℤ)):ℤ):ℝ)-sourcePivotTarget cfg J Δ l| ≤ _
    rw [log_int_prime_product]
    exact hh
  · have hjk := (scheduled_role_index_lt k j i.val).2 j b ha
    have hh := scheduled_anchor_atom_log_bounds cfg m j bulk top E i.val ⟨j,hjk⟩ b ha
      (fun a => h ⟨i,a⟩) (fun a => hmem ⟨i,a⟩)
    rw [ha]
    simp only [sourceRoleCenter,dite_eq_left hjk]
    change |Real.log (((∏ a,((h ⟨i,a⟩).val:ℤ)):ℤ):ℝ) - (cfg.1 (anchorCoordinate ⟨j,hjk⟩ b):ℝ)| ≤ _
    rw [log_int_prime_product]
    have h1 := sourceAtomWidth_ge_one k hc
    apply abs_le.mpr
    constructor <;> linarith

theorem source_copied_log_target (hj : j < k) (hc : 0 < c)
    (hlist : ∀ a, |((cfg.2 a).sum:ℝ)-configurationTarget logX J Δ cfg a| ≤ 6/c)
    (hlen : ∀ a, ((cfg.2 a).length:ℝ) ≤ 2*Real.exp (2*((1/10000:ℝ)*k)))
    (h : CopiedConstituent (schedule k j) j (sourceWidth cfg m) → PrimeUpTo Q)
    (hmem : ∀ a,h a ∈ scheduledPrimeShells k (sourceWidth cfg m)
      (configurationPrimeShells cfg m bulk top E) j (copiedConstituentOld _ _ _ a))
    (hbin : ∀ i : WordSlot k j,⌊Real.log (copiedSampleState (schedule k j) j
      (sourceWidth cfg m) h ⟨i.val,word_copied _ _ _ i.property.1 i.property.2⟩:ℝ)⌋=J) :
    |Real.log (((∏ i,copiedSampleState (schedule k j) j (sourceWidth cfg m) h i):ℤ):ℝ)-
      (sourcePivotTarget cfg J Δ j+Δ (j+1))| ≤ sourceCopiedWidth k c := by
  have hp (i : ScheduledCopiedSlots k j) :
      0 < (copiedSampleState (schedule k j) j (sourceWidth cfg m) h i : ℝ) :=
    by
      simp only [copiedSampleState,Int.cast_prod,Int.cast_natCast]
      exact Finset.prod_pos (fun a _ => by exact_mod_cast (primeUpTo_prime (h ⟨i,a⟩)).pos)
  rw [Int.cast_prod,Real.log_prod (fun i _ => (hp i).ne')]
  rw [← sourceRoleCenter_copied_total cfg J Δ hj]
  apply (abs_sum_scheduledCopied_sub_le_uniform k j hj _ (sourceRoleCenter cfg J Δ)
    (sourceAtomWidth k c) (source_copied_atom_target cfg m j bulk top E J Δ logX c hc
      hlist hlen h hmem hbin)).trans
  unfold sourceCopiedWidth
  apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (sourceAtomWidth_ge_one k hc))
  have hpow : (2:ℝ)^j ≤ 2^k := pow_le_pow_right₀ (by norm_num) hj.le
  have hn : ((k-(j+1):ℕ):ℝ) ≤ k := by exact_mod_cast Nat.sub_le k (j+1)
  linarith

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
