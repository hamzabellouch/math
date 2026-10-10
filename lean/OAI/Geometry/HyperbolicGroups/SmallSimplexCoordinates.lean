import Mathlib
import OAI.Geometry.HyperbolicGroups.VoltageEdges
import OAI.Geometry.HyperbolicGroups.EdgeCoordinates

namespace OAI

/-! Low-dimensional shared-face coordinates, in the actual barycentric carrier. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}

omit [DecidableEq V] in
lemma coordinate_le_one (x : Carrier K) (a : V) : x.val a ≤ 1 := by
  rw [←x.property.2.1]
  exact Finset.single_le_sum (fun i hi => x.property.1 i) (Finset.mem_univ a)

omit [Fintype V] in
lemma nonempty_pair_of_card_le_two {s : Finset V} (hs : s.Nonempty) (hc : s.card ≤ 2) :
    ∃ a b, s = {a,b} := by
  by_cases h2 : s.card = 2
  · obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp h2
    exact ⟨a,b,he⟩
  · obtain ⟨a,ha⟩ := hs
    refine ⟨a,a,?_⟩
    have h1 : s.card ≤ 1 := by omega
    ext j
    simp only [Finset.mem_insert,Finset.mem_singleton,or_self]
    exact ⟨fun hj => Finset.card_le_one.mp h1 j hj a ha,fun h => h.symm ▸ ha⟩

lemma simplex_sum_pair {a b : V} (hab : a ≠ b) (x : Voltage.closedFace (K := K) {a,b}) :
    x.val.val a + x.val.val b = 1 := by
  have hh := Finset.sum_subset (Finset.subset_univ ({a,b} : Finset V))
    (fun j hj hj' => x.property.2.2 j hj')
  simpa [Finset.sum_pair hab] using hh.trans x.property.2.1

namespace Voltage

def edgeParameter {a b : V} (x : closedFace (K := K) {a,b}) : I :=
  if a = b then 0 else ⟨x.val.val b,x.property.1 b,coordinate_le_one x.val b⟩

lemma edgeParameter_continuous (a b : V) :
    Continuous (edgeParameter (K := K) (a:=a) (b:=b)) := by
  unfold edgeParameter
  split_ifs
  · fun_prop
  · apply Continuous.subtype_mk
    exact (continuous_apply b).comp (continuous_subtype_val.comp continuous_subtype_val)

lemma edgePoint_parameter {a b : V} (h : {a,b} ∈ K.faces)
    (x : closedFace (K := K) {a,b}) : edgePoint h (edgeParameter x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  change (edgePath K h (edgeParameter x)).val j = x.val.val j
  rw [edgePath_coordinate]
  by_cases hab : a = b
  · subst b
    have hh : x.val.val a = 1 := by
      have hh := Finset.sum_subset (Finset.subset_univ ({a} : Finset V))
        (fun j hj hj' => x.property.2.2 j (by simpa using hj'))
      simpa using hh.trans x.property.2.1
    by_cases hj : j = a
    · subst j; simp [edgeParameter,hh]
    · simp [hj,x.property.2.2 j (by simp [hj])]
  · have hsum := simplex_sum_pair hab x
    by_cases hj : j = a
    · subst j; simp [edgeParameter,hab]; linarith
    · by_cases hjb : j = b
      · subst j; simp [edgeParameter,hab,hj]
      · simp [hj,hjb,x.property.2.2 j (by simp [hj,hjb])]

lemma closedFace_inter {s t : Finset V} (x : Carrier K)
    (hs : x ∈ closedFace s) (ht : x ∈ closedFace t) : x ∈ closedFace (s ∩ t) := by
  refine ⟨hs.1,hs.2.1,?_⟩
  intro a ha
  by_cases hsa : a ∈ s
  · exact ht.2.2 a (fun hta => ha (Finset.mem_inter.mpr ⟨hsa,hta⟩))
  · exact hs.2.2 a hsa

omit [DecidableEq V] in
lemma closedFace_nonempty {s : Finset V} (x : closedFace (K := K) s) : s.Nonempty := by
  by_contra hn
  have hz : ∀ a, x.val.val a = 0 := fun a => x.property.2.2 a (fun ha => hn ⟨a,ha⟩)
  have hh := x.property.2.1
  simp [hz] at hh

omit [Fintype V] in
lemma inter_card_le_two {s t : Finset V} (hs : s.card ≤ 3) (ht : t.card ≤ 3) (hne : s ≠ t) :
    (s ∩ t).card ≤ 2 := by
  by_contra hn
  have h1 := Finset.card_le_card (Finset.inter_subset_left (s₁:=s) (s₂:=t))
  have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁:=s) (s₂:=t))
  have h3 : s = s ∩ t := (Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)).symm
  have h4 : s ∩ t = t := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  exact hne (h3.trans h4)

end Voltage
end HyperbolicObstruction.FinitePolyhedron
end

end OAI
