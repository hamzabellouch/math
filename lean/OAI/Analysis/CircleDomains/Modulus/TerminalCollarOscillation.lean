import OAI.Analysis.CircleDomains.Topology.TerminalBoundaryLimits
import OAI.Analysis.CircleDomains.Selection.RoundHoleOffsets
import Mathlib.Topology.Order.Compact

namespace OAI

/-! Uniform oscillation on target collars, derived from the proved
assignment of target ends to physical terminal boundaries. No boundary
extension of the uniformizing map is assumed. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem TerminalComponentAssignment.inverse_boundary_neighborhood
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    {i : I} {O : Set Sphere} (hO : IsOpen O)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) ⊆ O) :
    ∃ W : Set Sphere, IsOpen W ∧ connectedComponentIn Vᶜ (a.point i) ⊆ W ∧
      ∀ y ∈ W ∩ V, fi y ∈ O := by
  let B : Set Sphere := {y | y ∈ V ∧ fi y ∉ O}
  refine ⟨(closure B)ᶜ, isClosed_closure.isOpen_compl, ?_, ?_⟩
  · intro y hy hyB
    obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp hyB
    have he := a.inverse_eventually_near_boundary hf hy hlim
      (Eventually.of_forall fun n => (hs n).1) hO hboundary
    obtain ⟨n, hn⟩ := he.exists
    exact (hs n).2 hn
  · intro y hy
    by_contra hn
    exact hy.1 (subset_closure (show y ∈ B from ⟨hy.2, hn⟩))

 theorem exists_open_oscillation_bound
    {X : Type*} [TopologicalSpace X] {K U : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (hU : IsOpen U) (hKU : K ⊆ U)
    (v : X → ℝ) (hv : ContinuousOn v U) (A : ℝ)
    (hA : ∀ x ∈ K, ∀ y ∈ K, |v x - v y| ≤ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ O : Set X, IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧
      ∀ x ∈ O, ∀ y ∈ O, |v x - v y| ≤ A + ε := by
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne (hv.mono hKU)
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne (hv.mono hKU)
  let O : Set X := U ∩ v ⁻¹' Ioo (v a - ε / 2) (v b + ε / 2)
  have hO : IsOpen O := hv.isOpen_inter_preimage hU isOpen_Ioo
  have hKO : K ⊆ O := by
    intro x hx
    refine ⟨hKU hx, ?_, ?_⟩
    · have hh : v a ≤ v x := hmin hx
      linarith
    · have hh : v x ≤ v b := hmax hx
      linarith
  refine ⟨O, hO, hKO, inter_subset_left, ?_⟩
  intro x hx y hy
  have hba := (abs_le.mp (hA b hb a ha)).2
  exact abs_le.mpr ⟨by linarith [hx.2.1, hy.2.2], by linarith [hx.2.2, hy.2.1]⟩

 theorem TerminalComponentAssignment.round_collar_oscillation
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (htarget : ((↑) : ℂ → Sphere) '' closedBall c r ⊆
      connectedComponentIn Vᶜ (a.point i))
    {U : Set Sphere} (hU : IsOpen U)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) ⊆ U)
    (v : Sphere → ℝ) (hv : ContinuousOn v U) (A : ℝ)
    (hA : ∀ x ∈ frontier (jordanInterior (T i)),
      ∀ y ∈ frontier (jordanInterior (T i)), |v (x : Sphere) - v (y : Sphere)| ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ closedBall c (r + δ), ∀ y ∈ closedBall c (r + δ),
      (x : Sphere) ∈ V → (y : Sphere) ∈ V →
      |v (fi (x : Sphere)) - v (fi (y : Sphere))| ≤ A + ε := by
  let K := ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i))
  have hK : IsCompact K :=
    ((isCompact_closure_jordanInterior (T i)).of_isClosed_subset
      isClosed_frontier frontier_subset_closure).image OnePoint.continuous_coe
  have hne : K.Nonempty := (isConnected_frontier_jordanInterior (T i)).nonempty.image _
  obtain ⟨O, hO, hKO, _, hosc⟩ := exists_open_oscillation_bound hK hne hU hboundary v hv A
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; exact hA x hx y hy) hε
  obtain ⟨W, hW, hcomp, hmap⟩ := a.inverse_boundary_neighborhood hf hO hKO
  have hin : closedBall c r ⊆ ((↑) : ℂ → Sphere) ⁻¹' W :=
    fun x hx => hcomp (htarget ⟨x, hx, rfl⟩)
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall c r).exists_cthickening_subset_open
    (hW.preimage OnePoint.continuous_coe) hin
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxV hyV
  have hxW : (x : Sphere) ∈ W := hδsub (by
    simpa only [cthickening_closedBall hδ.le hr, add_comm δ] using hx)
  have hyW : (y : Sphere) ∈ W := hδsub (by
    simpa only [cthickening_closedBall hδ.le hr, add_comm δ] using hy)
  exact hosc _ (hmap _ ⟨hxW, hxV⟩) _ (hmap _ ⟨hyW, hyV⟩)

end CircleDomainRigidity

end

end OAI
