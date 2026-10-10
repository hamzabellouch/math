import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.MarkedRow
import OAI.Combinatorics.TriangleRemoval.Queries.OrderedMarkedRow

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

noncomputable def finsetCandidateOrder {A : Type*} [DecidableEq A] (C : Finset A) : List C :=
  C.toList.attach.map (fun a => ⟨a.val,Finset.mem_toList.mp a.property⟩)

lemma finsetCandidateOrder_map {A : Type*} [DecidableEq A] (C : Finset A) :
    (finsetCandidateOrder C).map Subtype.val = C.toList := by
  simp only [finsetCandidateOrder,List.map_map,Function.comp_def]
  simp

lemma finsetCandidateOrder_perm {A : Type*} [DecidableEq A] (C : Finset A) :
    (finsetCandidateOrder C).Perm (Finset.univ : Finset C).toList := by
  have hn : (finsetCandidateOrder C).Nodup := List.Nodup.of_map Subtype.val (by
    rw [finsetCandidateOrder_map]
    exact Finset.nodup_toList _)
  apply (List.perm_ext_iff_of_nodup hn (Finset.nodup_toList _)).mpr
  intro a
  simp only [Finset.mem_toList,Finset.mem_univ,iff_true]
  apply List.mem_map.mpr
  exact ⟨⟨a.val,Finset.mem_toList.mpr a.property⟩,List.mem_attach _ _,by apply Subtype.ext; rfl⟩

namespace ExposureTree
variable {K A B V : Type*}
lemma exposeLabeled_relabel (key : B → K) (f : A → B) (as : List A) :
    mapOutput (List.map (fun p : A × V => (f p.1,p.2)))
      (exposeLabeled (key ∘ f) as) = exposeLabeled key (as.map f) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [exposeLabeled,List.map_cons,mapOutput,mapOutput_bind]
    congr 1
    funext v
    rw [← ih]
    rw [bind_mapOutput]
end ExposureTree

section CandidateKernel
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def requiredCandidates (H : τ → Finset ι)
    (required : List (ι × τ) → Bool) (address : List (ι × τ))
    (focus : Finset ι) (parent : Option τ) : Finset (gridCandidates H focus parent) :=
  Finset.univ.filter (fun a => required (a.val :: address))

noncomputable def markedChildKernel (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d : ℕ) (address : List (ι × τ))
    (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) (u : Fin N) : PMF (Bool × Bool) :=
  ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
    (markedGridQueryDepth H N required d u.val (a.val :: address)
      ((H a.val.2).erase a.val.1) (some a.val.2))

omit [Fintype ι] in
lemma candidate_clock_table (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (focus : Finset ι) (parent : Option τ) :
    (productPMF (fun _ : gridCandidates H focus parent => PMF.uniformOfFintype (Fin N))).map
      (fun ω => (finsetCandidateOrder (gridCandidates H focus parent)).map
        (fun a => (a.val,ω a))) =
    ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H focus parent).toList) := by
  let C := gridCandidates H focus parent
  let order := finsetCandidateOrder C
  have ho : order.Nodup := (finsetCandidateOrder_perm C).nodup_iff.mpr (Finset.nodup_toList _)
  have htable := ExposureTree.exposeLabeled_table
    (fun _ : τ => PMF.uniformOfFintype (Fin N)) (fun a : C => a.val.2)
    order ho (fun _ : C => PMF.uniformOfFintype (Fin N)) (by intros; rfl)
  have hm := congrArg (PMF.map (List.map (fun p : C × Fin N => (p.1.val,p.2)))) htable
  rw [PMF.map_comp,← ExposureTree.fresh_mapOutput] at hm
  simp only [Function.comp_def,List.map_map] at hm
  have he := ExposureTree.exposeLabeled_relabel (V := Fin N) Prod.snd
    (Subtype.val : C → ι × τ) order
  dsimp only [Function.comp_def] at he
  rw [he] at hm
  simpa only [order,C,finsetCandidateOrder_map] using hm

omit [Fintype ι] in

theorem markedGridQueryDepth_candidate_kernel (H : τ → Finset ι)
    (N : ℕ) [NeZero N] (required : List (ι × τ) → Bool)
    (d k : ℕ) (address : List (ι × τ)) (focus : Finset ι) (parent : Option τ) :
    ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
      (markedGridQueryDepth H N required (d+1) k address focus parent) =
    (productPMF (fun _ : gridCandidates H focus parent => PMF.uniformOfFintype (Fin N))).bind
      (fun ω => markedCheck (orderedMarkedRow
        (finsetCandidateOrder (gridCandidates H focus parent))
        (requiredCandidates H required address focus parent)
        (markedChildKernel H N required d address focus parent) k ω)) := by
  classical
  rw [markedGridQueryDepth,ExposureTree.fresh_bind,← candidate_clock_table H N focus parent,
    PMF.bind_map]
  congr 1
  funext ω
  dsimp only [Function.comp_def]
  rw [ExposureTree.fresh_checkMarked]
  simp only [List.map_map,Function.comp_def]
  let order := finsetCandidateOrder (gridCandidates H focus parent)
  let as := (order.map (fun a => (a.val,ω a))).mergeSort (fun a b => a.2.val ≤ b.2.val)
  have hp := markedCheck_map_priority as
    (fun p => required (p.1 :: address))
    (fun p => if p.2.val < k then ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
      (markedGridQueryDepth H N required d p.2.val (p.1 :: address)
        ((H p.1.2).erase p.1.1) (some p.1.2)) else PMF.pure (false,false))
    (fun _ => 0) (fun p => p.2.val)
  calc
    _ = markedCheck (as.map (fun p => (⟨required (p.1 :: address),
        if p.2.val < k then ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
          (markedGridQueryDepth H N required d p.2.val (p.1 :: address)
            ((H p.1.2).erase p.1.1) (some p.1.2)) else PMF.pure (false,false),0⟩ : MarkedChild))) := by
      congr 1
      apply List.map_congr_left
      intro p _
      split <;> rfl
    _ = _ := by
      rw [hp]
      congr 1
      dsimp only [as]
      rw [List.map_mergeSort (s := fun a b : MarkedChild => decide (a.priority ≤ b.priority))
        (by intros; rfl),List.map_map]
      unfold orderedMarkedRow
      congr 1
      apply List.map_congr_left
      intro a _
      dsimp [rowChild,markedChildKernel]
      simp only [requiredCandidates,Finset.mem_filter,Finset.mem_univ,true_and]
      cases required (a.val :: address) <;> rfl

end CandidateKernel
end SharpTerminalLeave

end

end OAI
