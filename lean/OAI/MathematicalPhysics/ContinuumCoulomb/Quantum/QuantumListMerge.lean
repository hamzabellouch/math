import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListGraph
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma

namespace OAI

/-! Canonical merging of a finite bond tape. A quadratic table of vertex pairs
gives a deterministic order and retains exactly the pairs occurring in the input. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge
open MediatorListProgram

abbrev Pair := ℕ × ℕ

def ordered (e : Bond) : Pair := (min e.1 e.2.1,max e.1 e.2.1)
def pairs (n : ℕ) : List Pair := (List.range n).product (List.range n)
def support (n : ℕ) (xs : List Bond) : List Pair :=
  (pairs n).filter (fun p => decide (p ∈ xs.map ordered))
def weight (xs : List Bond) (p : Pair) : ℚ :=
  (xs.map (fun e => if ordered e=p then e.2.2 else 0)).sum
def value (n : ℕ) (xs : List Bond) : List Bond :=
  (support n xs).map (fun p => (p.1,p.2,weight xs p))

theorem pairs_nodup (n : ℕ) : (pairs n).Nodup :=
  List.nodup_range.product List.nodup_range

theorem pairs_length (n : ℕ) : (pairs n).length=n*n := by
  exact (List.length_product (List.range n) (List.range n)).trans
    (congrArg₂ (·*·) List.length_range List.length_range)

theorem support_nodup (n : ℕ) (xs : List Bond) : (support n xs).Nodup :=
  (pairs_nodup n).filter _

theorem value_length (n : ℕ) (xs : List Bond) : (value n xs).length≤n*n := by
  simpa only [value,List.length_map,support,pairs_length] using
    ((List.length_filter_le (fun p => decide (p ∈ xs.map ordered)) (pairs n)))

theorem ordered_bounded {n : ℕ} {e : Bond} (h : e.1<n ∧ e.2.1<n) :
    (ordered e).1<n ∧ (ordered e).2<n := by
  exact ⟨(min_le_left _ _).trans_lt h.1,max_lt h.1 h.2⟩

theorem mem_support {n : ℕ} {xs : List Bond} (hb : SourceBondLists.bounded n xs) (p : Pair) :
    p ∈ support n xs ↔ p ∈ xs.map ordered := by
  simp only [support,List.mem_filter,decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hp
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    have h := ordered_bounded (hb e he)
    exact ⟨List.mem_product.mpr ⟨List.mem_range.mpr h.1,List.mem_range.mpr h.2⟩,
      List.mem_map.mpr ⟨e,he,rfl⟩⟩

theorem bounded (n : ℕ) (xs : List Bond) : SourceBondLists.bounded n (value n xs) := by
  intro e he
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  have hp' := (List.mem_filter.mp hp).1
  exact ⟨List.mem_range.mp (List.mem_product.mp hp').1,
    List.mem_range.mp (List.mem_product.mp hp').2⟩

theorem noLoops {n : ℕ} {xs : List Bond}
    (h : ∀ e ∈ xs, e.1≠e.2.1) : ∀ e ∈ value n xs, e.1≠e.2.1 := by
  intro e he
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  have hm := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨b,hb,hbp⟩ := List.mem_map.mp hm
  subst p
  change min b.1 b.2.1≠max b.1 b.2.1
  exact (min_lt_max.mpr (h b hb)).ne

theorem value_get (n : ℕ) (xs : List Bond) (i : Fin (value n xs).length) :
    (value n xs).get i =
      let p := (support n xs).get ⟨i.val,by simpa only [value,List.length_map] using i.isLt⟩
      (p.1,p.2,weight xs p) := by
  exact List.getElem_map _

end ContinuumCoulomb.QuantumListMerge

end

end OAI
