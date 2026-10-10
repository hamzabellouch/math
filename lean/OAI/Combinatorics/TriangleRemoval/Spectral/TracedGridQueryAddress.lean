import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.FreshLogExposeLabeled
import OAI.Combinatorics.TriangleRemoval.Spectral.FreshLogCheckNone2

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section TraceAddress
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem tracedGridQuery_address (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    ∀ a ∈ z.1.2, c.address <:+ a.address := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have heq : y = ((true,[c]),[]) := by simpa [ExposureTree.freshLog] using hy
    simp [heq]
  | succ d ih =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hwP := ExposureTree.freshLog_checkNoneTrace_forall ν
      (fun a : QueryCall ι τ => c.address <:+ a.address) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · intro b hb
          exact (List.suffix_cons p.1 c.address).trans (ih _ _ ha b hb)
        · have heq : a = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using ha
          simp [heq]) hw
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨[],rfl⟩
    · exact hwP a ha

lemma fork_addresses_ne {α : Type*} {p q : α} {base a b : List α} (hpq : p ≠ q)
    (ha : p :: base <:+ a) (hb : q :: base <:+ b) : a ≠ b := by
  intro hab
  subst b
  have hh := List.suffix_of_suffix_length_le ha hb (by simp)
  have heq := hh.eq_of_length (by simp)
  exact hpq (List.cons.inj heq).1

lemma child_address_ne {α : Type*} {p : α} {base a : List α}
    (ha : p :: base <:+ a) : base ≠ a := by
  intro h
  have hh := ha.length_le
  simp only [List.length_cons, ← h] at hh
  omega

theorem tracedGridQuery_address_nodup (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    (z.1.2.map QueryCall.address).Nodup := by
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
      (fun a b : QueryCall ι τ => a.address ≠ b.address) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · have hh := ih _ _ ha
          simpa only [List.Nodup, List.pairwise_map] using hh
        · have heq : a = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using ha
          simp [heq])
      (by
        apply List.pairwise_map.mpr
        apply hpair.imp
        intro p q hpq x hx y hy a ha b hb
        split_ifs at hx hy with hp hq
        · exact fork_addresses_ne hpq
            (tracedGridQuery_address H N d _ _ ν hx a ha)
            (tracedGridQuery_address H N d _ _ ν hy b hb)
        · have heq : y = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hy
          simp [heq] at hb
        · have heq : x = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hx
          simp [heq] at ha
        · have heq : x = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hx
          simp [heq] at ha) hw
    have hwP := ExposureTree.freshLog_checkNoneTrace_forall ν
      (fun a : QueryCall ι τ => c.address ≠ a.address) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · intro b hb
          exact child_address_ne (tracedGridQuery_address H N d _ _ ν ha b hb)
        · have heq : a = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using ha
          simp [heq]) hw
    simpa only [List.Nodup, List.map_cons, List.pairwise_cons, List.pairwise_map,
      List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      using (And.intro hwP hwR)

end TraceAddress
end SharpTerminalLeave

end

end OAI
