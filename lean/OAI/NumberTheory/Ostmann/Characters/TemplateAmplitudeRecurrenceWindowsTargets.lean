import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsAtoms
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWindowsRoles

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction Preliminaries HigherBiasSourceTargets
attribute [local instance] Classical.propDecidable

def sourcePivotTarget {k : ℕ} (cfg : SourceConfiguration k) (J : ℤ) (Δ : ℕ → ℝ) (j : ℕ) : ℝ :=
  pivotTarget k (J:ℝ) (configurationAnchorPair cfg) Δ j

def sourceRoleCenter {k : ℕ} (cfg : SourceConfiguration k) (J : ℤ) (Δ : ℕ → ℝ) : Role → ℝ
  | .word => J
  | .pivot j => sourcePivotTarget cfg J Δ j
  | .anchor j b => if h : j < k then (cfg.1 (anchorCoordinate ⟨j,h⟩ b):ℝ) else 0
  | .filler => 0

def sourceAtomWidth (k : ℕ) (c : ℝ) : ℝ := 6/c + 2*Real.exp (2*((1/10000:ℝ)*k)) + 1

def sourceCopiedWidth (k : ℕ) (c : ℝ) : ℝ := ((2:ℝ)^k+k+2)*sourceAtomWidth k c

theorem sourceAtomWidth_ge_one (k : ℕ) {c : ℝ} (hc : 0 < c) : 1 ≤ sourceAtomWidth k c := by
  unfold sourceAtomWidth
  have hd : 0 ≤ 6/c := div_nonneg (by norm_num) hc.le
  have he := Real.exp_pos (2*((1/10000:ℝ)*k))
  linarith

theorem sourceCopiedWidth_nonneg (k : ℕ) {c : ℝ} (hc : 0 < c) : 0 ≤ sourceCopiedWidth k c := by
  unfold sourceCopiedWidth
  exact mul_nonneg (by positivity) (zero_le_one.trans (sourceAtomWidth_ge_one k hc))

theorem configurationAnchorPair_eq_coordinates {k : ℕ} (cfg : SourceConfiguration k)
    (j : Fin k) : configurationAnchorPair cfg j.val =
      (cfg.1 (anchorCoordinate j false):ℝ) + (cfg.1 (anchorCoordinate j true):ℝ) := by
  simp only [configurationAnchorPair,dite_eq_left j.isLt]
  rfl

theorem sourceRoleCenter_copied_total {k j : ℕ} (cfg : SourceConfiguration k)
    (J : ℤ) (Δ : ℕ → ℝ) (hj : j < k) :
    copiedRoleTotal k j (sourceRoleCenter cfg J Δ) = sourcePivotTarget cfg J Δ j + Δ (j+1) := by
  unfold copiedRoleTotal
  simp only [sourceRoleCenter,dite_eq_left hj]
  have ha := configurationAnchorPair_eq_coordinates cfg ⟨j,hj⟩
  have ht := pivotTarget_recurrence hj (J:ℝ) (configurationAnchorPair cfg) Δ
  unfold sourcePivotTarget
  rw [ha] at ht
  linarith

theorem configurationTarget_pivot {k : ℕ} (cfg : SourceConfiguration k)
    (J : ℤ) (Δ : ℕ → ℝ) (logX : ℝ) (j : Fin k) :
    configurationTarget logX (J:ℝ) Δ cfg j.castSucc = sourcePivotTarget cfg J Δ j.val := by
  simp only [configurationTarget, Fin.val_castSucc, ite_eq_left j.isLt, sourcePivotTarget]

theorem scheduled_pivot_atom_target {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (J : ℤ) (Δ : ℕ → ℝ) (logX c : ℝ) (_hc : 0 < c)
    (hlist : ∀ a, |((cfg.2 a).sum:ℝ)-configurationTarget logX J Δ cfg a| ≤ 6/c)
    (hlen : ∀ a, ((cfg.2 a).length:ℝ) ≤ 2*Real.exp (2*((1/10000:ℝ)*k)))
    (i : (schedule k j).Slot) (l : Fin k) (hi : (schedule k j).role i = .pivot l.val)
    (q : Fin (sourceWidth cfg m ((schedule k j).role i)) → PrimeUpTo Q)
    (hq : ∀ a,q a ∈ scheduledPrimeShells k (sourceWidth cfg m)
      (configurationPrimeShells cfg m bulk top E) j ⟨i,a⟩) :
    |Real.log (characterTupleProduct q : ℝ)-sourcePivotTarget cfg J Δ l.val| ≤ sourceAtomWidth k c := by
  have hb := scheduled_pivot_atom_log_bounds cfg m j bulk top E i l hi q hq
  have ht := hlist l.castSucc
  rw [configurationTarget_pivot cfg J Δ logX l] at ht
  have hh := hlen l.castSucc
  obtain ⟨htl,htu⟩ := abs_le.mp ht
  apply abs_le.mpr
  unfold sourceAtomWidth
  constructor <;> linarith [Real.exp_pos (2*((1/10000:ℝ)*k)), div_nonneg (by norm_num : (0:ℝ)≤6) _hc.le]

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
