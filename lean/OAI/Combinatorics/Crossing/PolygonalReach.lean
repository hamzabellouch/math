import OAI.Combinatorics.Crossing.DrawingDefinition
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.Clopen
import Mathlib.Logic.Relation

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

def SegmentReach (O : Set Plane) (a b : Plane) : Prop :=
  Relation.ReflTransGen (fun x y => segment ℝ x y ⊆ O) a b

theorem segmentReach_mem {O : Set Plane} {a b : Plane} (ha : a ∈ O) (h : SegmentReach O a b) : b ∈ O := by
  induction h with
  | refl => exact ha
  | @tail b c hab hbc ih => exact hbc (right_mem_segment ℝ b c)

theorem isOpen_segmentReach (O : Set Plane) (hO : IsOpen O) (a : Plane) (ha : a ∈ O) :
    IsOpen {b | SegmentReach O a b} := by
  apply Metric.isOpen_iff.mpr
  intro b hb
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds (segmentReach_mem ha hb))
  refine ⟨ε,hε,?_⟩
  intro c hc
  apply Relation.ReflTransGen.tail hb
  exact ((convex_ball b ε).segment_subset (Metric.mem_ball_self hε) hc).trans hball

theorem isOpen_non_segmentReach (O : Set Plane) (hO : IsOpen O) (a : Plane) :
    IsOpen (O \ {b | SegmentReach O a b}) := by
  apply Metric.isOpen_iff.mpr
  intro b hb
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hb.1)
  refine ⟨ε,hε,?_⟩
  intro c hc
  refine ⟨hball hc,?_⟩
  intro hreach
  apply hb.2
  apply Relation.ReflTransGen.tail hreach
  exact ((convex_ball b ε).segment_subset hc (Metric.mem_ball_self hε)).trans hball

theorem segmentReach_of_path {a b : Plane} (γ : Path a b) (O : Set Plane)
    (hO : IsOpen O) (hγ : ∀ t, γ t ∈ O) : SegmentReach O a b := by
  have ha : a ∈ O := by simpa using hγ 0
  let A : Set unitInterval := {t | SegmentReach O a (γ t)}
  have hopen : IsOpen A := (isOpen_segmentReach O hO a ha).preimage γ.continuous
  have hcomp : IsOpen Aᶜ := by
    have heq : Aᶜ = γ ⁻¹' (O \ {x | SegmentReach O a x}) := by
      ext t
      simp only [A,Set.mem_compl_iff,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_sdiff,hγ t,true_and]
    rw [heq]
    exact (isOpen_non_segmentReach O hO a).preimage γ.continuous
  have hall : A=Set.univ := (show IsClopen A from ⟨by simpa using hcomp.isClosed_compl,hopen⟩).eq_univ ⟨0,by
    change SegmentReach O a (γ 0)
    rw [γ.source]
    exact Relation.ReflTransGen.refl⟩
  have hb : (1 : unitInterval) ∈ A := by rw [hall]; trivial
  change SegmentReach O a (γ 1) at hb
  rwa [γ.target] at hb

end Zarankiewicz

end

end OAI
