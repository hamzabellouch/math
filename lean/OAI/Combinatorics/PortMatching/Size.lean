import OAI.Combinatorics.PortMatching.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace OAI

/-! Perfect-matching-preserving port-path degree reduction for finite simple graphs. -/

noncomputable section
namespace Matching205

universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable instance graphAdjDecidable : DecidableRel (graph G).Adj :=
  fun _ _ => Classical.propDecidable _

private lemma size_vertex_ext {x y : Vertex G}
    (hbase : x.1 = y.1) (hpos : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨v, i⟩
  rcases y with ⟨w, j⟩
  dsimp at hbase hpos
  subst w
  congr 1
  exact Fin.ext hpos

private lemma size_port_injective (v : V) : Function.Injective (port G v) := by
  intro a b hab
  have h := congrArg (fun x : Vertex G => x.2.val) hab
  change 2 * ((Fintype.equivFin (G.neighborSet v)) a).val =
    2 * ((Fintype.equivFin (G.neighborSet v)) b).val at h
  apply (Fintype.equivFin (G.neighborSet v)).injective
  apply Fin.ext
  omega

private lemma size_external_base_ne {x y : Vertex G} (h : External G x y) :
    x.1 ≠ y.1 := by
  obtain ⟨h, _, _⟩ := h
  exact h.ne

private lemma size_external_unique {x y z : Vertex G}
    (hy : External G x y) (hz : External G x z) : y = z := by
  obtain ⟨hxy, hx, hy⟩ := hy
  obtain ⟨hxz, hx', hz⟩ := hz
  have hn := size_port_injective G x.1 (hx.symm.trans hx')
  have hbase : y.1 = z.1 := congrArg Subtype.val hn
  have transport (v w : V) (h : v = w) (hv : G.Adj v x.1) (hw : G.Adj w x.1) :
      port G v ⟨x.1, hv⟩ = port G w ⟨x.1, hw⟩ := by
    subst w
    rfl
  have hp := transport y.1 z.1 hbase hxy.symm hxz.symm
  exact hy.trans (hp.trans hz.symm)

private def size_neighborCode (x : Vertex G) (y : (graph G).neighborSet x) : Fin 3 := by
  classical
  exact if y.val.1 = x.1 then
    if y.val.2.val + 1 = x.2.val then 0 else 1
  else 2

private lemma size_neighborCode_injective (x : Vertex G) :
    Function.Injective (size_neighborCode G x) := by
  classical
  intro y z hc
  have hy : Internal G x y.val ∨ External G x y.val := y.property
  have hz : Internal G x z.val ∨ External G x z.val := z.property
  apply Subtype.ext
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · apply size_vertex_ext G (hy.1.symm.trans hz.1)
    have hv := congrArg Fin.val hc
    by_cases hyp : y.val.2.val + 1 = x.2.val <;>
      by_cases hzp : z.val.2.val + 1 = x.2.val
    all_goals simp [size_neighborCode, hy.1.symm, hz.1.symm, hyp, hzp] at hv
    all_goals rcases hy.2 with hy' | hy' <;> rcases hz.2 with hz' | hz' <;> omega
  · have hn : z.val.1 ≠ x.1 := (size_external_base_ne G hz).symm
    have hv := congrArg Fin.val hc
    by_cases hp : y.val.2.val + 1 = x.2.val <;>
      simp [size_neighborCode, hy.1.symm, hn, hp] at hv
  · have hn : y.val.1 ≠ x.1 := (size_external_base_ne G hy).symm
    have hv := congrArg Fin.val hc
    by_cases hp : z.val.2.val + 1 = x.2.val <;>
      simp [size_neighborCode, hz.1.symm, hn, hp] at hv
  · exact size_external_unique G hy hz

theorem graph_degree_le_three (x : Vertex G) : (graph G).degree x ≤ 3 := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  simpa using Fintype.card_le_of_injective (size_neighborCode G x)
    (size_neighborCode_injective G x)

theorem card_vertex_add_card (hpos : ∀ v : V, 0 < G.degree v) :
    Fintype.card (Vertex G) + Fintype.card V = 4 * G.edgeFinset.card := by
  classical
  have hfiber (v : V) : Fintype.card (Fin (2 * arity G v - 1)) + 1 =
      2 * G.degree v := by
    rw [card_fiber G v]
    have hv := hpos v
    omega
  calc
    Fintype.card (Vertex G) + Fintype.card V =
        ∑ v : V, (Fintype.card (Fin (2 * arity G v - 1)) + 1) := by
      simp [Vertex, Fintype.card_sigma, Finset.sum_add_distrib]
    _ = ∑ v : V, 2 * G.degree v := Finset.sum_congr rfl (fun v _ => hfiber v)
    _ = 2 * ∑ v : V, G.degree v := (Finset.mul_sum _ _ _).symm
    _ = 4 * G.edgeFinset.card := by
      rw [G.sum_degrees_eq_twice_card_edges]
      omega

theorem card_vertex (hpos : ∀ v : V, 0 < G.degree v) :
    Fintype.card (Vertex G) = 4 * G.edgeFinset.card - Fintype.card V := by
  have h := card_vertex_add_card G hpos
  omega

end Matching205

end

end OAI
