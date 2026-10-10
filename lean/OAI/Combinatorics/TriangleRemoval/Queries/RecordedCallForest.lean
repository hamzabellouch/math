import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.Child
import OAI.Combinatorics.TriangleRemoval.Queries.ForkAddressesNotSuffix

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

structure RecordedCallForest {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]
    (H : τ → Finset ι) (c : QueryCall ι τ) where
  size : ℕ
  call : Fin size → QueryCall ι τ
  root : Fin size
  root_eq : call root = c
  address_injective : Function.Injective (fun i => (call i).address)
  parent : (i : Fin size) → i ≠ root → Fin size
  is_child : ∀ i h, (call (parent i h)).Child H (call i)
  parent_lt : ∀ i h, parent i h < i

namespace RecordedCallForest
section General
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]
variable {H : τ → Finset ι} {c : QueryCall ι τ} (F : RecordedCallForest H c)

theorem parent_depth (i : Fin F.size) (h : i ≠ F.root) :
    (F.call (F.parent i h)).address.length < (F.call i).address.length := by
  rw [(F.is_child i h).address_length]
  omega

theorem parent_wellFounded :
    WellFounded (fun i j => ∃ h : j ≠ F.root, i = F.parent j h) := by
  apply (measure (fun i : Fin F.size => (F.call i).address.length)).wf.mono
  intro i j hij
  obtain ⟨h,rfl⟩ := hij
  exact F.parent_depth j h

theorem root_le (i : Fin F.size) : F.root ≤ i := by
  induction i using (measure (fun i : Fin F.size => i.val)).wf.induction with
  | h i ih =>
    by_cases hi : i = F.root
    · exact le_of_eq hi.symm
    · exact (ih (F.parent i hi) (F.parent_lt i hi)).trans (le_of_lt (F.parent_lt i hi))

theorem root_val : F.root.val = 0 := by
  by_contra hn
  have hs : 0 < F.size := lt_of_le_of_lt (Nat.zero_le _) F.root.isLt
  have hl := F.root_le ⟨0,hs⟩
  exact hn (Nat.eq_zero_of_le_zero hl)

theorem reachable_root (i : Fin F.size) :
    Relation.ReflTransGen (fun i j => ∃ h : j ≠ F.root, i = F.parent j h) F.root i := by
  induction i using F.parent_wellFounded.induction with
  | h i ih =>
    by_cases hi : i = F.root
    · subst i
      exact Relation.ReflTransGen.refl
    · exact (ih (F.parent i hi) ⟨hi,rfl⟩).tail ⟨hi,rfl⟩

end General
end RecordedCallForest

section ExtractForest
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def extractCallForest (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N))
    (z : (Bool × List (QueryCall ι τ)) × List τ)
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    RecordedCallForest H c := by
  classical
  have ht := tracedGridQuery_parents H N d k c ν hz
  have hnd := tracedGridQuery_address_nodup H N d k c ν hz
  let r := (List.mem_iff_get.mp ht.1).choose
  have hr : z.1.2.get r = c := (List.mem_iff_get.mp ht.1).choose_spec
  have hinj : Function.Injective (fun i : Fin z.1.2.length => (z.1.2.get i).address) := by
    intro i j he
    have hp : z.1.2.Pairwise (fun a b => a.address ≠ b.address) := by
      simpa only [List.Nodup,List.pairwise_map] using hnd
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (List.pairwise_iff_get.mp hp i j hlt) he
    · exact (List.pairwise_iff_get.mp hp j i hgt) he.symm
  have hp (i : Fin z.1.2.length) (hi : i ≠ r) :
      ∃ p : Fin z.1.2.length, (z.1.2.get p).Child H (z.1.2.get i) := by
    rcases ht.2 _ (List.get_mem _ _) with he | ⟨p,hp,hpc⟩
    · have hh : i = r := hinj (congrArg QueryCall.address (he.trans hr.symm))
      exact False.elim (hi hh)
    · obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hp
      exact ⟨j,hpc⟩
  exact ⟨z.1.2.length,z.1.2.get,r,hr,hinj,
    fun i hi => (hp i hi).choose, fun i hi => (hp i hi).choose_spec,
    fun i hi => tracedGridQuery_parent_before H N d k c ν hz i _ (hp i hi).choose_spec⟩

end ExtractForest
end SharpTerminalLeave

end

end OAI
