import OAI.NumberTheory.Ostmann.Tree.ArrangementGraph
import OAI.NumberTheory.Ostmann.Tree.BadPartitionCounts

namespace OAI

/-! # Counting bad permutations through their actual overlap components -/

namespace Ostmann

open scoped BigOperators Classical

def BadBulkArrangement {r m : ℕ} (e : Equiv.Perm (Fin r × Fin m)) : Prop :=
  3 * r < 4 * Fintype.card (arrangementGraph m e).ConnectedComponent

theorem badBulkArrangement_witness {r m : ℕ} (hm : 0 < m)
    (e : Equiv.Perm (Fin r × Fin m)) (he : BadBulkArrangement e) :
    ∃ w : BadPartitionWitness r,
      ∀ x : Fin r × Fin m, w.2.1.2 (e x).1 = w.2.1.1 x.1 := by
  let C := (arrangementGraph m e).ConnectedComponent
  let t := Fintype.card C
  let E : C ≃ Fin t := Fintype.equivFin C
  let f : Fin r → Fin t := E ∘ arrangementLeft e
  let g : Fin r → Fin t := E ∘ arrangementRight e
  have ht : t ≤ r := by
    simpa only [Fintype.card_fin] using arrangement_component_count_le hm e
  have hf : Function.Surjective f := E.surjective.comp (arrangementLeft_surjective hm e)
  have hg : Function.Surjective g := E.surjective.comp (arrangementRight_surjective hm e)
  have hb (c : Fin t) : Fintype.card {l : Fin r // f l = c} =
      Fintype.card {l : Fin r // g l = c} := by
    have hleft : {l : Fin r // f l = c} ≃
        {l : Fin r // arrangementLeft e l = E.symm c} :=
      Equiv.subtypeEquivRight (fun _ => E.eq_symm_apply.symm)
    have hright : {l : Fin r // g l = c} ≃
        {l : Fin r // arrangementRight e l = E.symm c} :=
      Equiv.subtypeEquivRight (fun _ => E.eq_symm_apply.symm)
    rw [Fintype.card_congr hleft, Fintype.card_congr hright]
    exact arrangement_component_balance hm e _
  have hd : 4 * (r - t) ≤ r := by
    change 3 * r < 4 * t at he
    omega
  refine ⟨⟨⟨t, Nat.lt_succ_of_le ht⟩, ⟨(f, g), hf, hg, hb, hd⟩⟩, ?_⟩
  intro x
  exact congrArg E (arrangement_components_match e x)

theorem card_badBulkArrangement_le {r m : ℕ} (hm : 0 < m) :
    Fintype.card {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} ≤
      Fintype.card (Σ w : BadPartitionWitness r, w.Matching m) := by
  choose w hw using fun e : {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} =>
    badBulkArrangement_witness hm e.1 e.2
  let f : {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} →
      Σ w : BadPartitionWitness r, w.Matching m := fun e => ⟨w e, ⟨e.1, hw e⟩⟩
  apply Fintype.card_le_of_injective f
  intro e e' h
  apply Subtype.ext
  exact congrArg (fun z : Σ w : BadPartitionWitness r, w.Matching m => z.2.1) h

/-- The arrangement count used in Section 9. The prefactor depends only
on the number of leaves r; all m-dependence is explicit. -/
theorem badBulkArrangement_count_bound {r m : ℕ} (hr : 1 ≤ r) (hm : 0 < m) :
    (Fintype.card {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} : ℝ) ≤
      ((r + 1) * r ^ (2 * r) : ℕ) * (m.factorial : ℝ) ^ r *
        Real.exp ((m : ℝ) * r * (Real.log r + 1) / 4) := by
  have hc : (Fintype.card {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} : ℝ) ≤
      Fintype.card (Σ w : BadPartitionWitness r, w.Matching m) := by
    exact_mod_cast card_badBulkArrangement_le hm
  apply hc.trans
  simpa only [badPartitionCost, mul_assoc] using badPartition_total_bound hr m

end Ostmann

end OAI
