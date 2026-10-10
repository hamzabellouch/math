import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureGenus
import OAI.Geometry.HyperbolicGroups.MappedPicture

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]
namespace PictureMap
variable (M : PictureMap D)

lemma switch_opposite (a : D) : M.switch a (M.edge a) = M := by
  refine PictureMap.ext (M := M.switch a (M.edge a)) (N := M) rfl ?_
  change swap a (M.edge a) * M.edge * swap a (M.edge a) = M.edge
  rw [mul_assoc,mul_swap_eq_swap_mul M.edge a (M.edge a),M.edge_edge,swap_comm (M.edge a) a]
  rw [← mul_assoc,swap_mul_self,one_mul]

lemma switch_edge_a_of_ne (a b : D) (hn : M.edge b ≠ a) :
    (M.switch a b).edge a = M.edge b := by
  simp only [switch,mul_apply,swap_apply_left,swap_apply_of_ne_of_ne hn (M.edge_ne b)]

lemma switch_edge_b_of_ne (a b : D) (hn : M.edge a ≠ b) :
    (M.switch a b).edge b = M.edge a := by
  simp only [switch,mul_apply,swap_apply_right,swap_apply_of_ne_of_ne (M.edge_ne a) hn]

lemma vertex_switch_order (a b : D) (hne : b ≠ M.edge a) :
    (M.switch a b).vertex = (M.vertex * swap a b) * swap (M.edge a) (M.edge b) := by
  have hab : a ≠ M.edge b := by
    intro he
    apply hne
    rw [he,M.edge_edge]
  have hdis : (swap (M.edge a) (M.edge b)).Disjoint (swap a b) := by
    apply disjoint_iff_eq_or_eq.mpr
    intro x
    by_cases ha : x = a
    · subst x
      exact Or.inl (swap_apply_of_ne_of_ne (M.edge_ne a).symm hab)
    by_cases hb : x = b
    · subst x
      exact Or.inl (swap_apply_of_ne_of_ne hne (M.edge_ne b).symm)
    exact Or.inr (swap_apply_of_ne_of_ne ha hb)
  rw [M.vertex_switch,mul_assoc,hdis.commute.eq,← mul_assoc]

variable [Fintype D]

/-- Genus-zero is preserved by ANY cross-pairing of two outgoing edges at a
single actual source vertex, even when some far vertex is the same source
vertex. This includes the switches used in elementary disk cancellation.
The radial case is the disjoint-far-vertices special case. -/
theorem switch_genusZero_general (hM : M.GenusZero) (a b : D)
    (hv : M.vertex.SameCycle a b) : (M.switch a b).GenusZero := by
  by_cases heq : a = b
  · subst b
    have hs : M.switch a a = M := by
      apply PictureMap.ext (M := M.switch a a) (N := M) rfl
      change swap a a * M.edge * swap a a = M.edge
      rw [swap_self]
      change (1 : Perm D) * M.edge * 1 = M.edge
      simp only [one_mul,mul_one]
    rwa [hs]
  by_cases hop : b = M.edge a
  · subst b
    rwa [M.switch_opposite]
  have hba : M.edge a ≠ b := Ne.symm hop
  have hab : M.edge b ≠ a := by
    intro he
    apply hop
    have hh := congrArg M.edge he
    simpa only [M.edge_edge] using hh
  let q := M.vertex * swap a b
  have hq : cycles q = cycles M.vertex + 1 := cycles_split_right _ heq hv
  have hnew := M.vertex_switch_order a b hop
  have hC := M.switch_components_card a b hv
  change M.euler = _ at hM
  change (M.switch a b).euler = _
  by_cases hf : q.SameCycle (M.edge a) (M.edge b)
  · have hc := cycles_split_right q (M.edge.injective.ne heq) hf
    have hE : (M.switch a b).euler = M.euler + 2 := by
      simp only [euler,switch_face,hnew]
      change cycles (q * swap (M.edge a) (M.edge b)) + _ - _ = _
      rw [hc,hq]; ring
    have he := (M.switch a b).euler_le
    split_ifs at hC <;> omega
  · have hc := cycles_merge_right q hf
    have hE : (M.switch a b).euler = M.euler := by
      simp only [euler,switch_face,hnew]
      change cycles (q * swap (M.edge a) (M.edge b)) + _ - _ = _
      omega
    have hf' : (M.switch a b).vertex.SameCycle (M.edge a) (M.edge b) := by
      rw [hnew]
      exact sameCycle_after_swap_right q hf
    have h1 : (M.switch a b).components a (M.edge b) := by
      rw [← M.switch_edge_a_of_ne a b hab]
      exact (M.switch a b).edge_le_components SameCycle.rfl.apply_right
    have h2 : (M.switch a b).components b (M.edge a) := by
      rw [← M.switch_edge_b_of_ne a b hba]
      exact (M.switch a b).edge_le_components SameCycle.rfl.apply_right
    have hsame : (M.switch a b).components a b :=
      (M.switch a b).components.trans' h1 ((M.switch a b).components.trans'
        ((M.switch a b).vertex_le_components hf'.symm)
        ((M.switch a b).components.symm' h2))
    rw [ite_eq_left hsame] at hC
    omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
