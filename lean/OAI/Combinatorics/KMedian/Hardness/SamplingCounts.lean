import Mathlib

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

theorem coordinate_sum {J I : Type} [Fintype J] [Fintype I] [DecidableEq J]
    (j : J) (f : I → ℕ) :
    (∑ s : J → I, f (s j)) = Fintype.card I ^ (Fintype.card J-1) * ∑ i, f i := by
  classical
  have hJ : Fintype.card {k : J // k ≠ j} = Fintype.card J-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    _ = ∑ p : I × ({k : J // k ≠ j} → I), f p.1 :=
      Fintype.sum_equiv (Equiv.funSplitAt j I) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Fintype.card_fun,hJ]
      rw [mul_sum]

theorem equal_pair_count {J I B : Type} [Fintype J] [Fintype I] [DecidableEq J]
    [DecidableEq B] (j k : J) (hjk : j ≠ k) (color : I → B) (M : ℕ)
    (hM : ∀ b, (univ.filter (fun i => color i = b)).card ≤ M) :
    (univ.filter (fun s : J → I => color (s j) = color (s k))).card ≤
      Fintype.card I ^ (Fintype.card J-1) * M := by
  classical
  have hJ : Fintype.card {k : J // k ≠ j} = Fintype.card J-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [card_filter]
  have he : (∑ s : J → I, if color (s j) = color (s k) then 1 else 0) =
      ∑ p : I × ({x : J // x ≠ j} → I),
        if color p.1 = color (p.2 ⟨k,hjk.symm⟩) then 1 else 0 :=
    Fintype.sum_equiv (Equiv.funSplitAt j I) _ _ (fun _ => rfl)
  rw [he,Fintype.sum_prod_type,sum_comm]
  calc
    _ ≤ ∑ _ : ({x : J // x ≠ j} → I), M := by
      apply sum_le_sum
      intro r _
      simpa only [sum_boole,Nat.cast_id] using hM (color (r ⟨k,hjk.symm⟩))
    _ = _ := by simp [hJ]

theorem sampled_agreement_count {J I B : Type} [Fintype J] [Fintype I]
    [DecidableEq J] [DecidableEq B] (color : I → B) (M : ℕ)
    (hM : ∀ b, (univ.filter (fun i => color i = b)).card ≤ M) :
    (univ.filter (fun s : J → I => ∃ j k, j ≠ k ∧ color (s j) = color (s k))).card ≤
      (Fintype.card J)^2 * Fintype.card I ^ (Fintype.card J-1) * M := by
  classical
  let E (j k : J) : Finset (J → I) :=
    univ.filter (fun s => j ≠ k ∧ color (s j) = color (s k))
  have he : (univ.filter (fun s : J → I => ∃ j k, j ≠ k ∧ color (s j) = color (s k))) =
      univ.biUnion (fun j => univ.biUnion (E j)) := by
    ext s
    simp [E]
  have hp (j k : J) : (E j k).card ≤ Fintype.card I ^ (Fintype.card J-1) * M := by
    by_cases hjk : j = k
    · subst k; simp [E]
    · have he : E j k = univ.filter (fun s : J → I => color (s j) = color (s k)) := by
        ext s; simp [E,hjk]
      rw [he]
      exact equal_pair_count j k hjk color M hM
  rw [he]
  calc
    _ ≤ ∑ j, (univ.biUnion (E j)).card := card_biUnion_le
    _ ≤ ∑ j, ∑ k, (E j k).card := sum_le_sum (fun _ _ => card_biUnion_le)
    _ ≤ ∑ _ : J, ∑ _ : J, Fintype.card I ^ (Fintype.card J-1) * M :=
      sum_le_sum (fun j _ => sum_le_sum (fun k _ => hp j k))
    _ = _ := by simp [pow_two]; ring

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
