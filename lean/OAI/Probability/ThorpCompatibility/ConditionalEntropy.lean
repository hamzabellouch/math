import Mathlib
import OAI.Probability.ThorpCompatibility.Entropy

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma map_mass_pos_iff (P : Law α) (f : α → β) (b : β) :
    0 < (P.map f).mass b ↔ ∃ a, f a = b ∧ 0 < P.mass a := by
  classical
  unfold map
  rw [Finset.sum_pos_iff_of_nonneg (fun a _ => by split_ifs <;> simp_all [P.nonneg])]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    split_ifs at ha with hab
    · exact ⟨a, hab, ha⟩
    · exact False.elim (lt_irrefl _ ha)
  · rintro ⟨a, hab, ha⟩
    exact ⟨a, by simpa [hab] using ha⟩

noncomputable def kernelJoint (P : Law γ) (K : γ → Law β) : Law (β × γ) where
  mass a := P.mass a.2 * (K a.2).mass a.1
  nonneg a := mul_nonneg (P.nonneg a.2) ((K a.2).nonneg a.1)
  total := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [← Finset.mul_sum, (K _).total, mul_one]
    exact P.total

lemma condEntropy_le_prediction (P : Law α) (X : α → β) (Y : α → γ)
    (K : γ → Law β) (hs : ∀ a, 0 < P.mass a → 0 < (K (Y a)).mass (X a)) :
    P.condEntropy X Y ≤ -P.mean (fun a => Real.log ((K (Y a)).mass (X a))) := by
  let J := P.map (fun a => (X a, Y a))
  let R := (P.map Y).kernelJoint K
  have hzero : ∀ b, R.mass b = 0 → J.mass b = 0 := by
    intro b hb
    by_contra hJ
    have hpos : 0 < J.mass b := lt_of_le_of_ne (J.nonneg b) (Ne.symm hJ)
    obtain ⟨a, ha, hPa⟩ := (P.map_mass_pos_iff (fun a => (X a, Y a)) b).mp hpos
    have hR : 0 < R.mass (X a, Y a) :=
      mul_pos (P.map_mass_pos Y hPa) (hs a hPa)
    rw [ha, hb] at hR
    exact lt_irrefl _ hR
  have h := J.relativeEntropy_nonneg R hzero
  have hmean : J.relativeEntropy R =
      P.mean (fun a => Real.log (P.condMass X Y a)) -
        P.mean (fun a => Real.log ((K (Y a)).mass (X a))) := by
    change J.mean (fun b => Real.log (J.mass b / R.mass b)) = _
    rw [P.mean_map, ← P.mean_sub]
    apply P.mean_congr_support
    intro a ha
    dsimp [J, R, kernelJoint, Function.comp_def, condMass]
    rw [Real.log_div (P.map_mass_pos _ ha).ne'
      (mul_pos (P.map_mass_pos Y ha) (hs a ha)).ne',
      Real.log_mul (P.map_mass_pos Y ha).ne' (hs a ha).ne',
      Real.log_div (P.map_mass_pos _ ha).ne' (P.map_mass_pos Y ha).ne']
    ring
  rw [hmean] at h
  rw [P.condEntropy_eq_mean]
  linarith

end Law
end ThorpCompatibility

end OAI
