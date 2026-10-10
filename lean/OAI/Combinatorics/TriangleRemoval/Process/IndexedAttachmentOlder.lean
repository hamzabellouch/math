import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.Address
import OAI.Combinatorics.TriangleRemoval.Process.IndexedWitnessCode

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma indexed_attachment_older {K s R : ℕ} {E : Graph K}
    {birth : Fin s → Fin K} (hb : ∀ i, (birth i).val = R+i.val)
    (hE : E ∈ seedPatternChoices K R) (F : PathForest s)
    (f : Fin s → Finset (Fin K)) (hf : f ∈ indexedAttachmentFamily E birth F) :
    ∀ i, ∀ x ∈ f i, x.val < (birth i).val := by
  have hvalid := (mem_indexedAttachmentFamily E birth F f).mp hf
  intro i
  induction i using (measure (fun i : Fin s => i.val)).wf.induction with
  | h i ih =>
    intro x hx
    have hi := hvalid.2 i
    cases hp : F.parent i with
    | none =>
      rw [hp] at hi
      have he : f i ∈ rootEdgeUniverse K R := (Finset.mem_powerset.mp (Finset.mem_filter.mp hE).1) hi
      have hxr := (mem_initialVertices K R x).mp ((Finset.mem_powersetCard.mp he).1 hx)
      rw [hb]
      omega
    | some p =>
      rw [hp] at hi
      obtain ⟨u,hu,he⟩ := hi
      rw [he] at hx
      have hpi := F.property i p hp
      have hu' := ih p hpi u hu
      have hbirth : (birth p).val < (birth i).val := by
        rw [hb p,hb i]
        omega
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hbirth
      · have he := Finset.mem_singleton.mp hx
        subst x
        exact lt_trans hu' hbirth

lemma indexed_triangle_key_injective {n K s R : ℕ} {E : Graph K}
    {birth : Fin s → Fin K} (hb : ∀ i, (birth i).val = R+i.val)
    (hE : E ∈ seedPatternChoices K R) (F : PathForest s)
    (f : Fin s → Finset (Fin K)) (hf : f ∈ indexedAttachmentFamily E birth F)
    (ψ : Fin K ↪ Fin n) : Function.Injective (indexedTriangleKey birth f ψ) := by
  intro i j he
  have hi : ψ (birth i) ∈ (indexedTriangleKey birth f ψ j).2 := by
    rw [← he]
    exact Finset.mem_insert_self _ _
  have hj : ψ (birth j) ∈ (indexedTriangleKey birth f ψ i).2 := by
    rw [he]
    exact Finset.mem_insert_self _ _
  have hle (a b : Fin s) (h : ψ (birth a) ∈ (indexedTriangleKey birth f ψ b).2) :
      a.val ≤ b.val := by
    change ψ (birth a) ∈ insert (ψ (birth b)) ((f b).image ψ) at h
    rcases Finset.mem_insert.mp h with h | h
    · have hh := congrArg Fin.val (ψ.injective h)
      rw [hb a,hb b] at hh
      omega
    · obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp h
      have hxe' := ψ.injective hxe
      subst x
      have hh := indexed_attachment_older hb hE F f hf b (birth a) hx
      rw [hb a,hb b] at hh
      omega
  exact Fin.ext (Nat.le_antisymm (hle i j hi) (hle j i hj))

end SharpTerminalLeave

open scoped BigOperators

end

end OAI
