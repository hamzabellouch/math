import OAI.NumberTheory.Ostmann.Conclusion.PartitionPermutations

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion

def overlapRelation {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) (a b : Fin r) : Prop :=
  ∃ u v : Fin m, (σ (a,u)).1 = (σ (b,v)).1

def OverlapComponent {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) :=
  Quotient (Relation.EqvGen.setoid (overlapRelation σ))

instance {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) : Finite (OverlapComponent σ) := by
  unfold OverlapComponent
  infer_instance

instance {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) : Fintype (OverlapComponent σ) :=
  Fintype.ofFinite _

instance {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) : DecidableEq (OverlapComponent σ) :=
  Classical.decEq _

def leftComponent {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m))
    (a : Fin r) : OverlapComponent σ := Quotient.mk _ a

def rightComponent {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m)
    (b : Fin r) : OverlapComponent σ :=
  leftComponent σ (σ.symm (b,⟨0,hm⟩)).1

theorem leftComponent_surjective {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) :
    Function.Surjective (leftComponent σ) := by
  exact Quotient.mk_surjective

theorem slot_component {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) (hm : 0 < m)
    (x : Fin r × Fin m) : leftComponent σ x.1 = rightComponent σ hm (σ x).1 := by
  apply Quotient.sound
  apply Relation.EqvGen.rel
  refine ⟨x.2,(σ.symm ((σ x).1,⟨0,hm⟩)).2,?_⟩
  simp only [Prod.mk.eta, Equiv.apply_symm_apply]

theorem component_card_balance {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m))
    (hm : 0 < m) (i : OverlapComponent σ) :
    Fintype.card {a // leftComponent σ a = i} =
      Fintype.card {b // rightComponent σ hm b = i} := by
  let e : PartitionMatching (fun x : Fin r × Fin m => leftComponent σ x.1)
      (fun x : Fin r × Fin m => rightComponent σ hm x.1) :=
    ⟨σ,fun x => (slot_component σ hm x).symm⟩
  have h := Fintype.card_congr (partitionMatchingEquiv _ _ e i)
  simp only [card_slotFiber] at h
  exact Nat.eq_of_mul_eq_mul_right hm h

theorem component_card_pos {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m))
    (i : OverlapComponent σ) : 0 < Fintype.card {a // leftComponent σ a = i} := by
  obtain ⟨a,ha⟩ := leftComponent_surjective σ i
  exact Fintype.card_pos_iff.mpr ⟨⟨a,ha⟩⟩

theorem component_cards_sum {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) :
    ∑ i : OverlapComponent σ, Fintype.card {a // leftComponent σ a = i} = r := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (leftComponent σ))
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

theorem overlapComponent_card_le {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) :
    Fintype.card (OverlapComponent σ) ≤ r := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_surjective (leftComponent σ) (leftComponent_surjective σ)

theorem component_matching_card {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m))
    (hm : 0 < m) :
    Nat.card (PartitionMatching (fun x : Fin r × Fin m => leftComponent σ x.1)
      (fun x : Fin r × Fin m => rightComponent σ hm x.1)) =
      ∏ i : OverlapComponent σ, (Fintype.card {a // leftComponent σ a = i} * m).factorial :=
  card_slotPartitionMatching _ _ (component_card_balance σ hm)

def BadArrangement {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) : Prop :=
  3*r < 4*Fintype.card (OverlapComponent σ)

end Ostmann.Conclusion

end

end OAI
