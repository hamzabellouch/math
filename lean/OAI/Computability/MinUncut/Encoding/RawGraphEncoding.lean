import Mathlib
import OAI.Computability.MinUncut.Graphs.CanonicalPathGraph

namespace OAI

section
namespace MinUncut.Costed.GraphRegisters
open MinUncut.PathRealization

def packDemand {N : ℕ} (d : Demand (Fin N)) : List ℕ :=
  [d.left.val,d.right.val,d.equal.toNat]
def packDemands {N : ℕ} (ds : List (Demand (Fin N))) : List ℕ := ds.flatMap packDemand

lemma packed_addresses {N : ℕ} (ds : List (Demand (Fin N))) (d : ℕ) (hd : d<ds.length) :
    ((packDemands ds).drop (3*d)).headI=ds[d].left.val ∧
    ((packDemands ds).drop (3*d+1)).headI=ds[d].right.val ∧
    ((packDemands ds).drop (3*d+2)).headI=ds[d].equal.toNat := by
  induction ds generalizing d with
  | nil => simp at hd
  | cons e ds ih =>
    cases d with
    | zero => simp [packDemands,packDemand]
    | succ d =>
      have hh : d<ds.length := by simpa using hd
      simpa only [packDemands,List.flatMap_cons,packDemand,List.cons_append,List.nil_append,
        Nat.mul_add,Nat.mul_one,Nat.add_assoc,List.drop_succ_cons,List.getElem_cons_succ,
        Nat.succ_eq_add_one] using ih d hh

lemma canonicalLocal_iff {N M : ℕ} (e : Fin M → Demand (Fin N)) (d : Fin M)
    (u v : Fin (N+M*3)) :
    (∃j:Fin 4, j.val<(if (e d).equal then 4 else 3) ∧
      ((u=number N M (ends e (d,j)).1 ∧ v=number N M (ends e (d,j)).2) ∨
       (v=number N M (ends e (d,j)).1 ∧ u=number N M (ends e (d,j)).2))) ↔
    localAdj N d.val (e d).left.val (e d).right.val (e d).equal.toNat u.val v.val := by
  simp only [show (4:ℕ)=3+1 from rfl,Fin.exists_fin_succ]
  simp only [Fin.val_zero,Fin.val_succ]
  cases h : (e d).equal <;>
    simp [h,ends,localAdj,endpoint,Fin.ext_iff,number_left,number_right,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,and_comm,or_assoc,or_comm,or_left_comm]

lemma rawLocal_pack {N : ℕ} (ds : List (Demand (Fin N))) (d : Fin ds.length) (u v : ℕ) :
    rawLocal N d.val (packDemands ds) u v=
      localAdj N d.val ds[d].left.val ds[d].right.val ds[d].equal.toNat u v := by
  obtain ⟨hL,hR,hE⟩ := packed_addresses ds d.val d.isLt
  simp only [rawLocal,hL,hR,hE,Fin.getElem_fin]

lemma rawCell_canonical {N : ℕ} (ds : List (Demand (Fin N))) (u v : Fin (N+ds.length*3)) :
    rawCell N ds.length (packDemands ds) u.val v.val=
      (canonicalAdjacent (fun d:Fin ds.length=>ds[d]) u v).toNat := by
  have he : (∃d<ds.length,rawLocal N d (packDemands ds) u.val v.val) ↔
      (∃d:Fin ds.length,∃j:Fin 4,j.val<(if ds[d].equal then 4 else 3) ∧
        ((u=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).1 ∧
          v=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).2) ∨
         (v=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).1 ∧
          u=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).2))) := by
    constructor
    · rintro ⟨d,hd,h⟩
      refine ⟨⟨d,hd⟩,(canonicalLocal_iff (fun d:Fin ds.length=>ds[d]) ⟨d,hd⟩ u v).mpr ?_⟩
      exact (rawLocal_pack ds ⟨d,hd⟩ u.val v.val).mp h
    · rintro ⟨d,h⟩
      refine ⟨d.val,d.isLt,?_⟩
      have hx := (canonicalLocal_iff (fun d:Fin ds.length=>ds[d]) d u v).mp h
      simpa only [←rawLocal_pack] using hx
  unfold rawCell canonicalAdjacent
  simp only [he]
  by_cases hh : ∃ d:Fin ds.length,∃j:Fin 4,j.val<(if ds[d].equal then 4 else 3) ∧
      ((u=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).1 ∧
        v=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).2) ∨
       (v=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).1 ∧
        u=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).2)) <;>
    simp only [hh,ite_true,ite_false,decide_true,decide_false,Bool.toNat_true,Bool.toNat_false]

end MinUncut.Costed.GraphRegisters

end

end OAI
