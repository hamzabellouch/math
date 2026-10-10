import Mathlib
import OAI.Computability.VertexCover.PCP.CloudPadding

namespace OAI

                                                                                                

namespace UniqueGames.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

def listEquiv {α : Type*} [BEq α] [LawfulBEq α] (xs : List α)
    (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) : α ≃ Fin xs.length where
  toFun a := ⟨xs.idxOf a, List.idxOf_lt_length_of_mem (complete a)⟩
  invFun i := xs.get i
  left_inv a := List.idxOf_get _
  right_inv i := by
    apply Fin.ext
    exact List.get_idxOf nodup i

@[simp] theorem listEquiv_val {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) (a : α) :
    (listEquiv xs nodup complete a).val = xs.idxOf a := rfl

@[simp] theorem listEquiv_symm_apply {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs)
    (i : Fin xs.length) : (listEquiv xs nodup complete).symm i = xs.get i := rfl

def cloudDarts (t : Table) (v : Fin t.vertices) : List (Fin t.darts) :=
  (List.finRange t.darts).filter (fun e => decide (t.rows[e].tail = v))

@[simp] theorem mem_cloudDarts (t : Table) (v : Fin t.vertices) (e : Fin t.darts) :
    e ∈ cloudDarts t v ↔ t.rows[e].tail = v := by
  simp [cloudDarts]

theorem cloudDarts_nodup (t : Table) (v : Fin t.vertices) :
    (cloudDarts t v).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange t.darts)

theorem cloudDarts_sublist (t : Table) (v : Fin t.vertices) :
    (cloudDarts t v).Sublist (List.finRange t.darts) := List.filter_sublist

def cloudSize (t : Table) (v : Fin t.vertices) : Nat := (cloudDarts t v).length

theorem cloudSize_le_darts (t : Table) (v : Fin t.vertices) :
    cloudSize t v ≤ t.darts := by
  simpa only [cloudSize, List.length_finRange] using (cloudDarts_sublist t v).length_le

def cloudSelect (t : Table) (v : Fin t.vertices) (i : Fin (cloudSize t v)) :
    Cloud (semantics t) v :=
  ⟨(cloudDarts t v).get i,
    (mem_cloudDarts t v _).1 (List.get_mem (cloudDarts t v) i)⟩

def cloudRank (t : Table) (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    Fin (cloudSize t v) :=
  ⟨(cloudDarts t v).idxOf e.val,
    List.idxOf_lt_length_of_mem ((mem_cloudDarts t v e.val).2 e.property)⟩

@[simp] theorem cloudSelect_val (t : Table) (v : Fin t.vertices)
    (i : Fin (cloudSize t v)) :
    (cloudSelect t v i).val = (cloudDarts t v).get i := rfl

@[simp] theorem cloudRank_val (t : Table) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) :
    (cloudRank t v e).val = (cloudDarts t v).idxOf e.val := rfl

@[simp] theorem cloudSelect_cloudRank (t : Table) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) : cloudSelect t v (cloudRank t v e) = e := by
  apply Subtype.ext
  exact List.idxOf_get (cloudRank t v e).isLt

@[simp] theorem cloudRank_cloudSelect (t : Table) (v : Fin t.vertices)
    (i : Fin (cloudSize t v)) : cloudRank t v (cloudSelect t v i) = i := by
  apply Fin.ext
  exact List.get_idxOf (cloudDarts_nodup t v) i

def cloudEquiv (t : Table) (v : Fin t.vertices) :
    Cloud (semantics t) v ≃ Fin (cloudSize t v) where
  toFun := cloudRank t v
  invFun := cloudSelect t v
  left_inv := cloudSelect_cloudRank t v
  right_inv := cloudRank_cloudSelect t v

theorem cloudSize_eq_card_cloud (t : Table) (v : Fin t.vertices) :
    cloudSize t v = Fintype.card (Cloud (semantics t) v) := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (cloudEquiv t v)).symm

theorem cloudDarts_eq_nil_iff (t : Table) (v : Fin t.vertices) :
    cloudDarts t v = [] ↔ ∀ e : Fin t.darts, t.rows[e].tail ≠ v := by
  simp only [List.eq_nil_iff_forall_not_mem, mem_cloudDarts]

theorem cloudSize_eq_zero_iff (t : Table) (v : Fin t.vertices) :
    cloudSize t v = 0 ↔ ∀ e : Fin t.darts, t.rows[e].tail ≠ v := by
  rw [cloudSize, List.length_eq_zero_iff, cloudDarts_eq_nil_iff]

theorem sum_cloudSize (t : Table) : (∑ v, cloudSize t v) = t.darts := by
  calc
    _ = ∑ v, Fintype.card (Cloud (semantics t) v) := by
      apply Finset.sum_congr rfl
      intro v _
      exact cloudSize_eq_card_cloud t v
    _ = Fintype.card (Fin t.darts) := CloudPadding.sum_card_cloud (semantics t)
    _ = t.darts := Fintype.card_fin t.darts

def oldCloudIndex (t : Table) (e : Fin t.darts) :
    Fin (cloudSize t t.rows[e].tail) := cloudRank t t.rows[e].tail ⟨e, rfl⟩

@[simp] theorem cloudSelect_oldCloudIndex (t : Table) (e : Fin t.darts) :
    (cloudSelect t t.rows[e].tail (oldCloudIndex t e)).val = e :=
  congrArg Subtype.val (cloudSelect_cloudRank t t.rows[e].tail ⟨e, rfl⟩)

abbrev PaddedCloud (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) :=
  Cloud (paddedGraph (semantics t) (fun u => Fin (padding u))) v

def paddedOld (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) : PaddedCloud t padding v :=
  ⟨Sum.inl e.val, e.property⟩

def paddedNew (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (i : Fin (padding v)) : PaddedCloud t padding v :=
  ⟨Sum.inr ⟨v, i⟩, rfl⟩

def paddedCloudEquiv (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) : PaddedCloud t padding v ≃ Fin (cloudSize t v + padding v) :=
  (CloudPadding.paddedCloudEquiv (semantics t) (fun u => Fin (padding u)) v).trans
    ((Equiv.sumCongr (cloudEquiv t v) (Equiv.refl (Fin (padding v)))).trans
      finSumFinEquiv)

def paddedCloudRank (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices) :
    PaddedCloud t padding v → Fin (cloudSize t v + padding v) :=
  paddedCloudEquiv t padding v

def paddedCloudSelect (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices) :
    Fin (cloudSize t v + padding v) → PaddedCloud t padding v :=
  (paddedCloudEquiv t padding v).symm

@[simp] theorem paddedCloudSelect_rank (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : PaddedCloud t padding v) :
    paddedCloudSelect t padding v (paddedCloudRank t padding v e) = e :=
  (paddedCloudEquiv t padding v).symm_apply_apply e

@[simp] theorem paddedCloudRank_select (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v)) :
    paddedCloudRank t padding v (paddedCloudSelect t padding v i) = i :=
  (paddedCloudEquiv t padding v).apply_symm_apply i

@[simp] theorem paddedCloudRank_old (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    paddedCloudRank t padding v (paddedOld t padding v e) =
      Fin.castAdd (padding v) (cloudRank t v e) := rfl

@[simp] theorem paddedCloudRank_new (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    paddedCloudRank t padding v (paddedNew t padding v i) =
      Fin.natAdd (cloudSize t v) i := rfl

@[simp] theorem paddedCloudRank_old_val (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    (paddedCloudRank t padding v (paddedOld t padding v e)).val =
      (cloudRank t v e).val := rfl

@[simp] theorem paddedCloudRank_new_val (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    (paddedCloudRank t padding v (paddedNew t padding v i)).val =
      cloudSize t v + i.val := rfl

@[simp] theorem paddedCloudSelect_castAdd (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (cloudSize t v)) :
    paddedCloudSelect t padding v (Fin.castAdd (padding v) i) =
      paddedOld t padding v (cloudSelect t v i) := by
  apply (paddedCloudEquiv t padding v).injective
  change (paddedCloudEquiv t padding v)
      ((paddedCloudEquiv t padding v).symm (Fin.castAdd (padding v) i)) = _
  rw [Equiv.apply_symm_apply]
  change Fin.castAdd (padding v) i =
    Fin.castAdd (padding v) (cloudRank t v (cloudSelect t v i))
  rw [cloudRank_cloudSelect]

@[simp] theorem paddedCloudSelect_natAdd (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    paddedCloudSelect t padding v (Fin.natAdd (cloudSize t v) i) =
      paddedNew t padding v i :=
  (paddedCloudEquiv t padding v).symm_apply_apply (paddedNew t padding v i)

theorem card_paddedCloud (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) :
    Fintype.card (PaddedCloud t padding v) = cloudSize t v + padding v := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (paddedCloudEquiv t padding v)

end UniqueGames.Foundations.PCP.PreprocessingCloudIndex

end OAI
