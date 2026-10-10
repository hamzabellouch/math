import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentClassBound

namespace OAI

/-! # Nilpotence detected by an action on a central filtration

The three subgroups lemma increases the depth of a commutator action. Once
the lower central series centralizes the last filtration term, a centralizer
bound puts it inside that term; the action then lowers it to the identity.
-/

namespace PolycyclicRecognition

open scoped commutatorElement
variable {G : Type} [Group G]

theorem commutator_commutator_le_of_rotate (H₁ H₂ H₃ N : Subgroup G) [N.Normal]
    (h₁ : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h₂ : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  have hm (S : Subgroup G) : S ≤ N ↔ S.map q = ⊥ := by
    rw [eq_bot_iff, Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  apply (hm _).mpr
  rw [Subgroup.map_commutator, Subgroup.map_commutator]
  apply Subgroup.commutator_commutator_eq_bot_of_rotate
  · simpa only [Subgroup.map_commutator] using (hm _).mp h₁
  · simpa only [Subgroup.map_commutator] using (hm _).mp h₂

theorem lowerCentralSeries_action_depth (K : Subgroup G) (U : ℕ → Subgroup G)
    [∀ i, (U i).Normal]
    (hstep : ∀ i, ⁅K, U (i + 1)⁆ ≤ U i) (n i : ℕ) :
    ⁅K.lowerCentralSeries n, U (i + n + 1)⁆ ≤ U i := by
  induction n generalizing i with
  | zero => simpa only [Subgroup.lowerCentralSeries_zero, Nat.add_zero] using hstep i
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    apply commutator_commutator_le_of_rotate
    · have hs : ⁅K, U (i + (n + 1) + 1)⁆ ≤ U (i + n + 1) := by
        exact hstep (i + n + 1)
      calc
        ⁅⁅K, U (i + (n + 1) + 1)⁆, K.lowerCentralSeries n⁆ ≤
            ⁅U (i + n + 1), K.lowerCentralSeries n⁆ := Subgroup.commutator_mono_left hs
        _ = ⁅K.lowerCentralSeries n, U (i + n + 1)⁆ := Subgroup.commutator_comm _ _
        _ ≤ U i := ih i
    · have hs : ⁅U (i + (n + 1) + 1), K.lowerCentralSeries n⁆ ≤ U (i + 1) := by
        rw [Subgroup.commutator_comm]
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i + 1)
      exact (Subgroup.commutator_mono_left hs).trans (by
        rw [Subgroup.commutator_comm]
        exact hstep i)

theorem nilpotent_of_central_filtration_action (K : Subgroup G) (U : ℕ → Subgroup G)
    [∀ i, (U i).Normal] (hmono : Monotone U) (hzero : U 0 = ⊥)
    (hstep : ∀ i, ⁅K, U (i + 1)⁆ ≤ U i) (c : ℕ)
    (hcent : Subgroup.centralizer (U c : Set G) ≤ U c) : Group.IsNilpotent K := by
  have hz : ⁅K.lowerCentralSeries c, U c⁆ = ⊥ := by
    apply eq_bot_iff.mpr
    calc
      ⁅K.lowerCentralSeries c, U c⁆ ≤ ⁅K.lowerCentralSeries c, U (c + 1)⁆ :=
        Subgroup.commutator_mono_right (hmono (Nat.le_succ c))
      _ ≤ U 0 := by simpa only [Nat.zero_add] using lowerCentralSeries_action_depth K U hstep c 0
      _ = ⊥ := hzero
  have hdeep : K.lowerCentralSeries c ≤ U c :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hz).trans hcent
  have hdown : ∀ j, j ≤ c → K.lowerCentralSeries (c + j) ≤ U (c - j) := by
    intro j
    induction j with
    | zero => simpa only [Nat.add_zero, Nat.sub_zero] using fun _ : 0 ≤ c => hdeep
    | succ j ih =>
      intro hj
      have he : c - j = (c - (j + 1)) + 1 := by omega
      calc
        K.lowerCentralSeries (c + (j + 1)) = ⁅K.lowerCentralSeries (c + j), K⁆ := by
          rw [← Nat.add_assoc, Subgroup.lowerCentralSeries_succ]
        _ ≤ ⁅U (c - j), K⁆ := Subgroup.commutator_mono_left (ih (by omega))
        _ = ⁅K, U ((c - (j + 1)) + 1)⁆ := by rw [he, Subgroup.commutator_comm]
        _ ≤ U (c - (j + 1)) := hstep _
  apply (Subgroup.isNilpotent_iff_lowerCentralSeries K).mpr
  refine ⟨c + c, eq_bot_iff.mpr ?_⟩
  simpa only [Nat.sub_self, hzero] using hdown c le_rfl

end PolycyclicRecognition

end OAI
