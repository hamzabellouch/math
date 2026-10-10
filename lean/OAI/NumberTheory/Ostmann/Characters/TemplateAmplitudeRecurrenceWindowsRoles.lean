import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsRolesBasic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

@[simp] theorem scheduledCopiedRoleEquiv_apply (k j : ℕ) (hj : j < k)
    (r : ScheduledCopiedRoles k j) :
    scheduledCopiedRoleEquiv k j hj r = scheduledCopiedRoleMap k j hj r := rfl

def copiedRoleTotal (k j : ℕ) (f : Role → ℝ) : ℝ :=
  (2:ℝ)^j * f .word + (∑ r ∈ Finset.Ico (j+1) k, f (.pivot r)) +
    f (.anchor j false) + f (.anchor j true)

theorem sum_scheduledCopied_role (k j : ℕ) (hj : j < k) (f : Role → ℝ) :
    (∑ i : ScheduledCopiedSlots k j, f ((schedule k j).role i.val)) =
      (2:ℝ)^j * f .word + (∑ r ∈ Finset.Ico (j+1) k, f (.pivot r)) +
        f (.anchor j false) + f (.anchor j true) := by
  rw [← (scheduledCopiedRoleEquiv k j hj).sum_comp
    (fun i : ScheduledCopiedSlots k j => f ((schedule k j).role i.val))]
  simp only [Fintype.sum_sum_type, scheduledCopiedRoleEquiv_apply,
    scheduledCopiedRoleMap_word, scheduledCopiedRoleMap_pivot, scheduledCopiedRoleMap_anchor,
    Finset.sum_const, Finset.card_univ, active_word_card, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat, Fintype.sum_bool]
  rw [← Finset.sum_subtype (Finset.Ico (j+1) k) (fun _ => Iff.rfl)
    (fun r => f (.pivot r))]
  ring

theorem sum_scheduledCopied_role_eq_total (k j : ℕ) (hj : j < k) (f : Role → ℝ) :
    (∑ i : ScheduledCopiedSlots k j, f ((schedule k j).role i.val)) =
      copiedRoleTotal k j f :=
  sum_scheduledCopied_role k j hj f

theorem sum_scheduledCopied_le (k j : ℕ) (hj : j < k)
    (a : ScheduledCopiedSlots k j → ℝ) (f : Role → ℝ)
    (ha : ∀ i, a i ≤ f ((schedule k j).role i.val)) :
    (∑ i, a i) ≤ copiedRoleTotal k j f := by
  rw [← sum_scheduledCopied_role_eq_total k j hj f]
  exact Finset.sum_le_sum (fun i _ => ha i)

theorem abs_sum_scheduledCopied_sub_le (k j : ℕ) (hj : j < k)
    (a : ScheduledCopiedSlots k j → ℝ) (center width : Role → ℝ)
    (ha : ∀ i, |a i - center ((schedule k j).role i.val)| ≤
      width ((schedule k j).role i.val)) :
    |(∑ i, a i) - copiedRoleTotal k j center| ≤ copiedRoleTotal k j width := by
  rw [← sum_scheduledCopied_role_eq_total k j hj center, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (sum_scheduledCopied_le k j hj _ width ha)

theorem copiedRoleTotal_const (k j : ℕ) (c : ℝ) :
    copiedRoleTotal k j (fun _ => c) = ((2:ℝ)^j + (k-(j+1):ℕ) + 2) * c := by
  simp only [copiedRoleTotal, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  ring

theorem abs_sum_scheduledCopied_sub_le_uniform (k j : ℕ) (hj : j < k)
    (a : ScheduledCopiedSlots k j → ℝ) (center : Role → ℝ) (ε : ℝ)
    (ha : ∀ i, |a i - center ((schedule k j).role i.val)| ≤ ε) :
    |(∑ i, a i) - copiedRoleTotal k j center| ≤
      ((2:ℝ)^j + (k-(j+1):ℕ) + 2) * ε := by
  simpa only [copiedRoleTotal_const] using
    abs_sum_scheduledCopied_sub_le k j hj a center (fun _ => ε) ha

end Ostmann.Characters.Template

end

end OAI
