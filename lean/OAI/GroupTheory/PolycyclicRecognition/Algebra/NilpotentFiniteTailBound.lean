import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Group.Subgroup.Finite

namespace OAI

/-! # A finite tail in a nilpotent lower central series has bounded length -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem lowerCentralSeries_succ_lt_of_ne_bot (n : ℕ)
    (hn : (⊤ : Subgroup G).lowerCentralSeries n ≠ ⊥) :
    (⊤ : Subgroup G).lowerCentralSeries (n + 1) < (⊤ : Subgroup G).lowerCentralSeries n := by
  refine lt_of_le_of_ne ((⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n)) ?_
  intro he
  have hsame (k : ℕ) : (⊤ : Subgroup G).lowerCentralSeries (n + k) =
      (⊤ : Subgroup G).lowerCentralSeries n := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.add_succ, Subgroup.lowerCentralSeries_succ, ih]
      exact he
  apply hn
  rw [← hsame (Group.nilpotencyClass G)]
  apply eq_bot_iff.mpr
  exact ((⊤ : Subgroup G).lowerCentralSeries_antitone
    (Nat.le_add_left (Group.nilpotencyClass G) n)).trans_eq
    Subgroup.lowerCentralSeries_nilpotencyClass

theorem lowerCentralSeries_eq_bot_of_finite_tail (T : Subgroup G) [Finite T]
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n ≤ T) :
    (⊤ : Subgroup G).lowerCentralSeries (n + Nat.card T) = ⊥ := by
  let L (k : ℕ) := (⊤ : Subgroup G).lowerCentralSeries (n + k)
  have hLT (k : ℕ) : L k ≤ T :=
    ((⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_add_right n k)).trans hn
  let (k : ℕ) : Finite (L k) := Finite.of_injective (Subgroup.inclusion (hLT k))
    (Subgroup.inclusion_injective _)
  have hb (k : ℕ) (hk : L k ≠ ⊥) : Nat.card (L k) + k ≤ Nat.card T := by
    induction k with
    | zero => simpa only [add_zero] using Subgroup.card_le_of_le (hLT 0)
    | succ k ih =>
      have hk' : L k ≠ ⊥ := by
        intro he
        apply hk
        apply eq_bot_iff.mpr
        exact ((⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)).trans_eq he
      have hi := ih hk'
      have hs : Nat.card (L (k + 1)) < Nat.card (L k) :=
        Subgroup.card_lt_of_lt (lowerCentralSeries_succ_lt_of_ne_bot (n + k) hk')
      omega
  by_contra h
  have hbound := hb (Nat.card T) h
  have hp : 0 < Nat.card (L (Nat.card T)) := Nat.card_pos
  omega

theorem nilpotencyClass_le_quotient_add_finite_kernel (T : Subgroup G) [T.Normal] [Finite T] :
    Group.nilpotencyClass G ≤ Group.nilpotencyClass (G ⧸ T) + Nat.card T := by
  apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
  apply lowerCentralSeries_eq_bot_of_finite_tail T
  have hm : ((⊤ : Subgroup G).lowerCentralSeries (Group.nilpotencyClass (G ⧸ T))).map
      (QuotientGroup.mk' T) = ⊥ := by
    rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top, QuotientGroup.range_mk']
    exact Subgroup.lowerCentralSeries_nilpotencyClass
  simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm

end PolycyclicRecognition

end

end OAI
