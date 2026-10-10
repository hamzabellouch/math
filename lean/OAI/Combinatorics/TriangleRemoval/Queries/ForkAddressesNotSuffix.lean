import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.Child
import OAI.Combinatorics.TriangleRemoval.Spectral.TracedGridQueryAddress

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
section ChronologicalTrace
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

lemma fork_addresses_not_suffix {α : Type*} {p q : α} {base a b : List α}
    (hpq : p ≠ q) (ha : p :: base <:+ a) (hb : q :: base <:+ b) : ¬ b <:+ a := by
  intro hba
  have hh := List.suffix_of_suffix_length_le ha (hb.trans hba) (by simp)
  have heq := hh.eq_of_length (by simp)
  exact hpq (List.cons.inj heq).1

lemma child_address_not_suffix {α : Type*} {p : α} {base a : List α}
    (ha : p :: base <:+ a) : ¬ a <:+ base := by
  intro hab
  have h₁ := ha.length_le
  have h₂ := hab.length_le
  simp only [List.length_cons] at h₁
  omega

theorem tracedGridQuery_no_later_ancestor (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    (z.1.2.Pairwise (fun a b => ¬ b.address <:+ a.address)) := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have heq : y = ((true,[c]),[]) := by simpa [ExposureTree.freshLog] using hy
    simp [heq]
  | succ d ih =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hxvals := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).1
    have hnd : (x.1.map Prod.fst).Nodup := by rw [hxvals]; exact Finset.nodup_toList _
    have hsnd := ((List.mergeSort_perm x.1 (fun a b => a.2.val ≤ b.2.val)).map Prod.fst).nodup_iff.mpr hnd
    have hpair : (x.1.mergeSort (fun a b => a.2.val ≤ b.2.val)).Pairwise
        (fun a b => a.1 ≠ b.1) := by
      simpa only [List.Nodup, List.pairwise_map] using hsnd
    have hwR := ExposureTree.freshLog_checkNoneTrace_pairwise ν
      (fun a b : QueryCall ι τ => ¬ b.address <:+ a.address) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · exact ih _ _ ha
        · have heq : a = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using ha
          simp [heq])
      (by
        apply List.pairwise_map.mpr
        apply hpair.imp
        intro p q hpq x hx y hy a ha b hb
        split_ifs at hx hy with hp hq
        · exact fork_addresses_not_suffix hpq
            (tracedGridQuery_address H N d _ _ ν hx a ha)
            (tracedGridQuery_address H N d _ _ ν hy b hb)
        · have heq : y = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hy
          simp [heq] at hb
        · have heq : x = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hx
          simp [heq] at ha
        · have heq : x = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hx
          simp [heq] at ha) hw
    have hwP := ExposureTree.freshLog_checkNoneTrace_forall ν
      (fun a : QueryCall ι τ => ¬ a.address <:+ c.address) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · intro b hb
          exact child_address_not_suffix (tracedGridQuery_address H N d _ _ ν ha b hb)
        · have heq : a = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using ha
          simp [heq]) hw
    exact List.pairwise_cons.mpr ⟨hwP,hwR⟩

theorem tracedGridQuery_parent_before (H : τ → Finset ι) (N d k : ℕ)
    (c : QueryCall ι τ) (ν : τ → PMF (Fin N))
    {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support)
    (i j : Fin z.1.2.length) (h : (z.1.2.get j).Child H (z.1.2.get i)) : j < i := by
  have ho := tracedGridQuery_no_later_ancestor H N d k c ν hz
  obtain ⟨p,_,he⟩ := h
  have hs : (z.1.2.get j).address <:+ (z.1.2.get i).address := by
    rw [he]
    exact List.suffix_cons _ _
  rcases lt_trichotomy j i with hlt | rfl | hgt
  · exact hlt
  · have hlen := congrArg (fun a => a.address.length) he
    simp only [List.length_cons] at hlen
    omega
  · exact False.elim ((List.pairwise_iff_get.mp ho i j hgt) hs)

end ChronologicalTrace
end SharpTerminalLeave

end

end OAI
