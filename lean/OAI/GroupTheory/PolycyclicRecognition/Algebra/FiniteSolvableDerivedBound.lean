import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocallyBoundedDerivedSeries
import Mathlib.GroupTheory.IndexNormal

namespace OAI

/-! # Explicit derived-length bounds for finite soluble quotients -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem finite_solvable_derivedSeries_card [Finite G] [Group.IsSolvable G] :
    derivedSeries G (Nat.card G) = ⊥ := by
  have hb (n : ℕ) (hn : derivedSeries G n ≠ ⊥) :
      Nat.card (derivedSeries G n) + n ≤ Nat.card G := by
    induction n with
    | zero => simpa only [derivedSeries_zero, add_zero] using (⊤ : Subgroup G).card_le_card_group
    | succ n ih =>
      have hn' : derivedSeries G n ≠ ⊥ := by
        intro he
        apply hn
        simp only [derivedSeries_succ, he, Subgroup.commutator_bot_left]
      have hs := Subgroup.card_lt_of_lt (Group.IsSolvable.commutator_lt_of_ne_bot hn')
      have hi := ih hn'
      change Nat.card (derivedSeries G (n + 1)) < Nat.card (derivedSeries G n) at hs
      omega
  by_contra h
  have hh := hb (Nat.card G) h
  have hp : 0 < Nat.card (derivedSeries G (Nat.card G)) := Nat.card_pos
  omega

theorem normalCore_index_le_factorial (H : Subgroup G) [H.FiniteIndex] :
    H.normalCore.index ≤ H.index.factorial := by
  rw [Subgroup.normalCore_eq_ker, Subgroup.index_ker, Subgroup.index_eq_card, ← Nat.card_perm]
  exact Subgroup.card_le_card_group _

theorem derivedSeries_add_le_ambient (H : Subgroup G) (n r : ℕ)
    (hn : derivedSeries G n ≤ H) : derivedSeries G (n + r) ≤ ambientDerivedSeries H r := by
  induction r with
  | zero => simpa only [add_zero, ambientDerivedSeries_zero] using hn
  | succ r ih =>
    rw [Nat.add_succ, derivedSeries_succ, ambientDerivedSeries_succ]
    exact Subgroup.commutator_mono ih ih

theorem solvable_derivedSeries_bound_of_finiteIndex [Group.IsSolvable G]
    (H : Subgroup G) [H.FiniteIndex] (b r : ℕ) (hb : H.index ≤ b)
    (hr : derivedSeries H r = ⊥) : derivedSeries G (b.factorial + r) = ⊥ := by
  let N := H.normalCore
  let q := QuotientGroup.mk' N
  have hNi : N.index ≤ b.factorial :=
    (normalCore_index_le_factorial H).trans (Nat.factorial_le hb)
  have hq : derivedSeries (G ⧸ N) b.factorial = ⊥ := by
    apply eq_bot_iff.mpr
    have hi : Nat.card (G ⧸ N) ≤ b.factorial := by
      simpa only [← Subgroup.index_eq_card] using hNi
    exact (derivedSeries_antitone (G ⧸ N) hi).trans_eq finite_solvable_derivedSeries_card
  have hn : derivedSeries G b.factorial ≤ H := by
    apply le_trans _ H.normalCore_le
    change derivedSeries G b.factorial ≤ N
    rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff]
    rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective N), hq]
  apply eq_bot_iff.mpr
  have hd := derivedSeries_add_le_ambient H b.factorial r hn
  simpa only [ambientDerivedSeries, hr, Subgroup.map_bot] using hd

end PolycyclicRecognition

end

end OAI
