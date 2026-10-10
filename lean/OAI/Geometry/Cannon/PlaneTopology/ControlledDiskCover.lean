import Mathlib
import OAI.Geometry.Cannon.Boundary.PolynomialPacking

namespace OAI

section
section
section
section
section
namespace CannonRegularDisk
open Metric
open Set Metric Finset

variable {X : Type*} [MetricSpace X] [CompactSpace X]
attribute [local instance] Classical.propDecidable

theorem controlled_disk_cover {Q : ℕ} {C c : ℝ}
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q C)
    (hc : 0<c) (hc1 : c≤1)
    (hdisks : ∀ (x : X) (s : ℝ), 0<s → s≤1 →
      ∃ U : Set X, IsRegularDisk U ∧ ball x (c*s) ⊆ U ∧ closure U ⊆ ball x s) :
    ∃ B : ℕ, ∀ s : ℝ, 0<s → s≤1/2 →
      ∃ (T : Finset X) (U : T → Set X),
        (∀ i j : T, i≠j → (c/2)*s≤dist i.val j.val) ∧
        (∀ i, IsRegularDisk (U i) ∧ ball i.val (c*s) ⊆ U i ∧ closure (U i) ⊆ ball i.val s) ∧
        (∀ x : X, ∃ i, x ∈ U i) ∧
        (∀ i, ((Finset.univ : Finset T).filter (fun j => (closure (U i) ∩ closure (U j)).Nonempty)).card≤B) ∧
        ∀ x : X, ((Finset.univ : Finset T).filter (fun i => x ∈ closure (U i))).card≤B := by
  classical
  obtain ⟨B,hB⟩ := exists_nat_ge (C*(4/c)^Q)
  refine ⟨B,?_⟩
  intro s hs hs1
  have hcs : 0<(c/2)*s := mul_pos (half_pos hc) hs
  obtain ⟨T,hsep,hnet,_⟩ := CannonNet.exists_compact_net (X:=X) ((c/2)*s) hcs
  choose U hU hinner houter using fun i : T => hdisks i.val s hs (by linarith)
  have hsep' (i j : T) (hij : i≠j) : (c/2)*s≤dist i.val j.val :=
    hsep i.val i.property j.val j.property (fun h => hij (Subtype.ext h))
  have hcover (x : X) : ∃ i : T, x ∈ U i := by
    obtain ⟨p,hp,hd⟩ := hnet x
    refine ⟨⟨p,hp⟩,hinner ⟨p,hp⟩ ?_⟩
    change dist x p<c*s
    have hhalf : (c/2)*s<c*s := by nlinarith [mul_pos hc hs]
    exact hd.trans_lt hhalf
  have hdegree (i : T) :
      ((Finset.univ : Finset T).filter (fun j => (closure (U i) ∩ closure (U j)).Nonempty)).card≤B := by
    let S : Finset T := Finset.univ.filter (fun j => (closure (U i) ∩ closure (U j)).Nonempty)
    have hh := CannonPacking.indexed_packing Q C hpack (fun i : T => i.val) S i.val
      (2*s) ((c/2)*s) hcs (by nlinarith) (by linarith) (by
        intro j hj
        obtain ⟨z,hzi,hzj⟩ := (Finset.mem_filter.mp hj).2
        have hi := houter i hzi
        have hj := houter j hzj
        change dist z i.val<s at hi
        change dist z j.val<s at hj
        have ht := dist_triangle i.val z j.val
        rw [dist_comm i.val z] at ht
        linarith) (fun i _ j _ hij => hsep' i j hij)
    have heq : (2*s)/((c/2)*s)=4/c := by field_simp; ring
    rw [heq] at hh
    exact_mod_cast hh.trans hB
  refine ⟨T,U,hsep',fun i => ⟨hU i,hinner i,houter i⟩,hcover,hdegree,?_⟩
  intro x
  obtain ⟨i,hi⟩ := hcover x
  apply (Finset.card_le_card ?_).trans (hdegree i)
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,subset_closure hi,(Finset.mem_filter.mp hj).2⟩
end CannonRegularDisk

end
end
end
end
end

end OAI
