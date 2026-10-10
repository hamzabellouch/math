import OAI.Analysis.CircleDomains.Uniformization.FiniteUniformization

namespace OAI

/-!
# Finite uniformization of the actual terminal-disk complement

The complementary components are exactly the closed physical terminal
caps. In particular they are finite and nondegenerate. The published
finite circle theorem therefore applies after compact metric
uniformization; the resulting map is conformal on the retained core.
-/

open Set Function Filter
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def closedTerminalCap (H : ℂ ≃ₜ ℂ) : Set Sphere :=
  ((↑) : ℂ → Sphere) '' closure (jordanInterior H)

def openCompletedRegion {I : Type*} (H : I → ℂ ≃ₜ ℂ) : Set Sphere :=
  (⋃ i, closedTerminalCap (H i))ᶜ

theorem isCompact_closedTerminalCap (H : ℂ ≃ₜ ℂ) : IsCompact (closedTerminalCap H) :=
  (isCompact_closure_jordanInterior H).image OnePoint.continuous_coe

theorem isPreconnected_closedTerminalCap (H : ℂ ≃ₜ ℂ) : IsPreconnected (closedTerminalCap H) :=
  (isConnected_jordanInterior H).isPreconnected.closure.image _ OnePoint.continuous_coe.continuousOn

theorem nontrivial_closedTerminalCap (H : ℂ ≃ₜ ℂ) : (closedTerminalCap H).Nontrivial := by
  have hzero : H 0 ∈ closure (jordanInterior H) := by
    rw [closure_jordanInterior]
    exact ⟨0, by simp, rfl⟩
  have hone : H 1 ∈ closure (jordanInterior H) := by
    rw [closure_jordanInterior]
    exact ⟨1, by simp, rfl⟩
  refine ⟨(H 0 : ℂ), ⟨H 0, hzero, rfl⟩, (H 1 : ℂ), ⟨H 1, hone, rfl⟩, ?_⟩
  intro heq
  exact zero_ne_one (H.injective (OnePoint.coe_injective heq))

theorem disjoint_closedTerminalCaps {I : Type*} (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    Pairwise (Disjoint on fun i => closedTerminalCap (H i)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro p ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hyx : y = x := OnePoint.coe_injective heq
  exact Set.disjoint_left.mp (hdisj hij) hx (hyx ▸ hy)

theorem isOpen_openCompletedRegion {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ) :
    IsOpen (openCompletedRegion H) :=
  (isClosed_iUnion_of_finite fun i => (isCompact_closedTerminalCap (H i)).isClosed).isOpen_compl

theorem isConnected_openCompletedRegion {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    IsConnected (openCompletedRegion H) := by
  let S : Set ℂ := (⋃ i, closure (jordanInterior (H i)))ᶜ
  have hS : IsPreconnected S := isPreconnected_exterior_finite_jordanInteriors H hdisj
  have hinf : (∞ : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' S) := by
    have hmem : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ∈ S := by
      rw [coclosedCompact_eq_cocompact]
      exact (isCompact_iUnion fun i => isCompact_closure_jordanInterior (H i)).compl_mem_cocompact
    exact mem_closure_of_tendsto OnePoint.tendsto_coe_infty
      (hmem.mono fun z hz => ⟨z, hz, rfl⟩)
  have hsub : ((↑) : ℂ → Sphere) '' S ⊆ openCompletedRegion H := by
    rintro _ ⟨z, hz, rfl⟩ hb
    obtain ⟨i, x, hx, heq⟩ := mem_iUnion.mp hb
    have hxz : x = z := OnePoint.coe_injective heq
    exact hz (mem_iUnion.mpr ⟨i, hxz ▸ hx⟩)
  have hupper : openCompletedRegion H ⊆ closure (((↑) : ℂ → Sphere) '' S) := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
      apply subset_closure
      refine ⟨z, ?_, rfl⟩
      intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hp (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)
  refine ⟨⟨∞, ?_⟩, (hS.image _ OnePoint.continuous_coe.continuousOn).subset_closure hsub hupper⟩
  intro hb
  obtain ⟨i, z, _, heq⟩ := mem_iUnion.mp hb
  exact OnePoint.coe_ne_infty z heq

theorem uniformize_finite_completion_after_homeomorphism
    (hfinite : FiniteCircleUniformization)
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {W : Set Sphere} (e : Sphere ≃ₜ Sphere)
    (hW : W ⊆ openCompletedRegion H) (he : IsConformalOn e W) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ BijOn f (openCompletedRegion H) V ∧ IsConformalOn f W ∧
        IsConformalEquivalence (f ∘ e.symm) (e '' openCompletedRegion H) V := by
  apply circle_model_after_homeomorphism hfinite
    (isOpen_openCompletedRegion H) (isConnected_openCompletedRegion H hdisj)
    (fun i => closedTerminalCap (H i))
    (fun i => (isCompact_closedTerminalCap (H i)).isClosed)
    (fun i => isPreconnected_closedTerminalCap (H i)) (disjoint_closedTerminalCaps H hdisj)
    (fun i => nontrivial_closedTerminalCap (H i)) (compl_compl _) e hW he

end CircleDomainRigidity.FiniteTransfer

end

end OAI
