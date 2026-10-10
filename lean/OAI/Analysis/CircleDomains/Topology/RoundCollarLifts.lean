import OAI.Analysis.CircleDomains.Modulus.TerminalCollarOscillation
import OAI.Analysis.CircleDomains.Topology.RoundDiskStokes

namespace OAI

/-! The actual zero-period real lift on a target collar is the source
branch composed with the inverse finite model. Its oscillation follows
from the terminal assignment, not from a boundary extension. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem unitCircleParam_one_eq_zero (c : ℂ) (r : ℝ) :
    unitCircleParam c r 1 = unitCircleParam c r 0 := by
  simpa only [unitCircleParam, mul_one, mul_zero, zero_add] using (periodic_circleMap c r) 0

 theorem unitCircleParam_mem_round_exterior
    {I : Type*} (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i + ρ)))
    (i : I) (t : ℝ) : unitCircleParam (c i) (r i + ρ) t ∉ ⋃ j, closedBall (c j) (r j) := by
  have hs : unitCircleParam (c i) (r i + ρ) t ∈ sphere (c i) (r i + ρ) :=
    circleMap_mem_sphere _ (by linarith [hr i]) _
  rintro hm
  obtain ⟨j, hj⟩ := mem_iUnion.mp hm
  by_cases hij : i = j
  · subst j
    have he := mem_sphere.mp hs
    have hl := mem_closedBall.mp hj
    linarith
  · exact Set.disjoint_left.mp (hd hij) (sphere_subset_closedBall hs)
      (closedBall_subset_closedBall (by linarith : r j ≤ r j + ρ) hj)

 theorem TerminalComponentAssignment.round_collar_mapsTo
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (htarget : ((↑) : ℂ → Sphere) '' closedBall c r ⊆
      connectedComponentIn Vᶜ (a.point i))
    {U : Set Sphere} (hU : IsOpen U)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) ⊆ U) :
    ∃ δ > 0, ∀ x ∈ closedBall c (r + δ), (x : Sphere) ∈ V → fi (x : Sphere) ∈ U := by
  obtain ⟨W, hW, hcomp, hmap⟩ := a.inverse_boundary_neighborhood hf hU hboundary
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall c r).exists_cthickening_subset_open
    (hW.preimage OnePoint.continuous_coe) (fun x hx => hcomp (htarget ⟨x, hx, rfl⟩))
  refine ⟨δ, hδ, fun x hx hxV => hmap x ?_⟩
  exact ⟨hδsub (by simpa only [cthickening_closedBall hδ.le hr, add_comm δ] using hx), hxV⟩

 def roundCollarRealLift (fi : Sphere → Sphere) (v : Sphere → ℝ)
    (c : ℂ) (r : ℝ) (t : ℝ) : ℝ := v (fi (unitCircleParam c r t : Sphere))

 theorem TerminalComponentAssignment.exists_round_collar_lifts
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ)
    (i : I) (htarget : ((↑) : ℂ → Sphere) '' closedBall (c i) (r i) ⊆
      connectedComponentIn Vᶜ (a.point i))
    {U : Set Sphere} (hU : IsOpen U)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) ⊆ U)
    (v : Sphere → ℝ) (hv : ContinuousOn v U) (w : Sphere → UnitAddCircle)
    (hproj : ∀ x ∈ U, (v x : UnitAddCircle) = w x)
    (A : ℝ) (hA : ∀ x ∈ frontier (jordanInterior (T i)),
      ∀ y ∈ frontier (jordanInterior (T i)), |v (x : Sphere) - v (y : Sphere)| ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ρ ∈ Ioc (0 : ℝ) δ,
      Continuous (roundCollarRealLift fi v (c i) (r i + ρ)) ∧
      (∀ t, (roundCollarRealLift fi v (c i) (r i + ρ) t : UnitAddCircle) =
        w (fi (unitCircleParam (c i) (r i + ρ) t : Sphere))) ∧
      roundCollarRealLift fi v (c i) (r i + ρ) 1 = roundCollarRealLift fi v (c i) (r i + ρ) 0 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, |roundCollarRealLift fi v (c i) (r i + ρ) t -
        roundCollarRealLift fi v (c i) (r i + ρ) 0| ≤ A + ε := by
  obtain ⟨δU, hδU, hmap⟩ := a.round_collar_mapsTo hf i (c i) (hr i) htarget hU hboundary
  obtain ⟨δA, hδA, hosc⟩ := a.round_collar_oscillation hf i (c i) (hr i) htarget
    hU hboundary v hv A hA hε
  obtain ⟨δG, hδG, hgeom⟩ := exists_common_round_hole_offset c r hr hd isOpen_univ
    (fun _ => subset_univ _)
  refine ⟨min δU (min δA δG), lt_min hδU (lt_min hδA hδG), ?_⟩
  intro ρ hρ
  have hρU : ρ ≤ δU := hρ.2.trans (min_le_left _ _)
  have hρA : ρ ≤ δA := hρ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρG : ρ ≤ δG := hρ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdisj := (hgeom ρ ⟨hρ.1, hρG⟩).2
  have hV (t : ℝ) : (unitCircleParam (c i) (r i + ρ) t : Sphere) ∈ V := by
    change unitCircleParam (c i) (r i + ρ) t ∈ ((↑) : ℂ → Sphere) ⁻¹' V
    rw [hext]
    exact unitCircleParam_mem_round_exterior c r hr hρ.1 hdisj i t
  have hc (t : ℝ) : unitCircleParam (c i) (r i + ρ) t ∈ closedBall (c i) (r i + ρ) :=
    sphere_subset_closedBall (circleMap_mem_sphere _ (by linarith [hr i, hρ.1]) _)
  have hsource (t : ℝ) : fi (unitCircleParam (c i) (r i + ρ) t : Sphere) ∈ U :=
    hmap _ (closedBall_subset_closedBall (add_le_add le_rfl hρU) (hc t)) (hV t)
  refine ⟨?_, fun t => hproj _ (hsource t), ?_, ?_⟩
  · apply continuous_iff_continuousAt.mpr
    intro t
    have hcurve : Continuous (fun s : ℝ => (unitCircleParam (c i) (r i + ρ) s : Sphere)) :=
      OnePoint.continuous_coe.comp (contDiff_unitCircleParam _ _).continuous
    have hfic : ContinuousAt fi (unitCircleParam (c i) (r i + ρ) t : Sphere) :=
      (hf.smooth_inv _ (hV t)).1
    have hic : ContinuousAt (fun s : ℝ => fi (unitCircleParam (c i) (r i + ρ) s : Sphere)) t :=
      hfic.comp (f := fun s : ℝ => (unitCircleParam (c i) (r i + ρ) s : Sphere)) hcurve.continuousAt
    exact (hv.continuousAt (hU.mem_nhds (hsource t))).comp
      (f := fun s : ℝ => fi (unitCircleParam (c i) (r i + ρ) s : Sphere)) hic
  · unfold roundCollarRealLift
    rw [unitCircleParam_one_eq_zero]
  · intro t _
    exact hosc _ (closedBall_subset_closedBall (add_le_add le_rfl hρA) (hc t))
      _ (closedBall_subset_closedBall (add_le_add le_rfl hρA) (hc 0)) (hV t) (hV 0)

end CircleDomainRigidity

end

end OAI
