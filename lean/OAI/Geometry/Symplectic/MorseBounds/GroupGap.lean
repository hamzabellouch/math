import Mathlib

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace ArnoldCounterexample.Nondegenerate.GroupGap

theorem coordinate_patterns_injective (S : Type*) [Group S] [Nontrivial S]
    {k : ℕ} (T : Finset (Fin k → S))
    (hT : Subgroup.closure (T : Set (Fin k → S)) = ⊤) :
    Function.Injective (fun i : Fin k => fun g : T => (g : Fin k → S) i) := by
  classical
  intro i j hij
  by_contra hne
  let D : Subgroup (Fin k → S) :=
    { carrier := {g | g i = g j}
      one_mem' := rfl
      mul_mem' := by
        intro a b ha hb
        exact congrArg₂ (· * ·) ha hb
      inv_mem' := by
        intro a ha
        exact congrArg Inv.inv ha }
  have hle : Subgroup.closure (T : Set (Fin k → S)) ≤ D :=
    (Subgroup.closure_le D).mpr (fun g hg => congrFun hij ⟨g, hg⟩)
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  have hx : Function.update (fun _ : Fin k => (1 : S)) i s ∈ D :=
    hle (by rw [hT]; trivial)
  change Function.update (fun _ : Fin k => (1 : S)) i s i =
    Function.update (fun _ : Fin k => (1 : S)) i s j at hx
  exact hs (by simpa [hne, Ne.symm hne] using hx)

theorem factors_le_card_pow_rank (S : Type*) [Group S] [Fintype S] [Nontrivial S]
    (k : ℕ) : k ≤ Fintype.card S ^ Group.rank (Fin k → S) := by
  classical
  obtain ⟨T, hcard, hgen⟩ := Group.rank_spec (Fin k → S)
  have h := Fintype.card_le_of_injective _ (coordinate_patterns_injective S T hgen)
  simpa only [Fintype.card_fin, Fintype.card_fun, Fintype.card_coe, hcard] using h

theorem group_gap (S : Type*) [Group S] [Fintype S] [Nontrivial S]
    {k m : ℕ} (h : Fintype.card S ^ m < k) :
    m < Group.rank (Fin k → S) := by
  by_contra hn
  have hr : Group.rank (Fin k → S) ≤ m := Nat.le_of_not_gt hn
  have hp := Nat.pow_le_pow_right (n := Fintype.card S) Fintype.card_pos hr
  exact (not_lt_of_ge ((factors_le_card_pow_rank S k).trans hp)) h

lemma card_A5 : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [card_alternatingGroup, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem A5_power_rank_gap {k : ℕ} (hk : 60 ^ (16 * 61) < k) :
    16 * 61 < Group.rank (Fin k → alternatingGroup (Fin 5)) := by
  apply group_gap (alternatingGroup (Fin 5))
  simpa only [card_A5] using hk

theorem exists_A5_power_rank_gap :
    ∃ k : ℕ, 0 < k ∧ 16 * 61 < Group.rank (Fin k → alternatingGroup (Fin 5)) := by
  obtain ⟨k, hk⟩ := exists_gt (60 ^ (16 * 61) : ℕ)
  exact ⟨k, (Nat.zero_le _).trans_lt hk, A5_power_rank_gap hk⟩

end ArnoldCounterexample.Nondegenerate.GroupGap

end

end OAI
