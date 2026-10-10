import OAI.Analysis.CircleDomains.Topology.SaturatedDisks

namespace OAI

/-!
# Connected-complement neighborhoods on the concrete sphere

Finite points use ordinary round disks. Infinity uses complements of closed
round disks. Thus every open sphere neighborhood contains the closure of an
open neighborhood with connected complement, as needed for contour filling.
-/

open Set Filter Function Metric
open scoped Topology OnePoint

namespace CircleDomainRigidity

theorem infty_mem_closure_image_of_unbounded {S : Set ℂ}
    (hS : ¬ Bornology.IsBounded S) :
    (∞ : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' S) := by
  by_contra h
  have hc := isCompact_finite_preimage isClosed_closure h
  apply hS
  apply hc.isBounded.subset
  intro z hz
  exact subset_closure (mem_image_of_mem _ hz)

theorem isConnected_complex_exterior_closedBall_center (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IsConnected (closedBall c R)ᶜ := by
  have heq : (fun z : ℂ => z + c) '' (closedBall (0 : ℂ) R)ᶜ = (closedBall c R)ᶜ := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [mem_closedBall, dist_eq_norm] using hw
    · intro hz
      refine ⟨z - c, ?_, sub_add_cancel z c⟩
      simpa [mem_closedBall, dist_eq_norm] using hz
  rw [← heq]
  exact (isConnected_complex_exterior_closedBall hR).image _
    (continuous_id.add_const c).continuousOn

private theorem unbounded_complex_exterior (c : ℂ) (R : ℝ) :
    ¬ Bornology.IsBounded (closedBall c R)ᶜ := by
  intro h
  have hb := (isBounded_closedBall (x := c) (r := R)).union h
  rw [union_compl_self] at hb
  exact NormedSpace.unbounded_univ ℝ ℂ hb

theorem isConnected_sphere_exterior_closedBall (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IsConnected ((((↑) : ℂ → Sphere) '' closedBall c R)ᶜ) := by
  let E : Set ℂ := (closedBall c R)ᶜ
  have hE : IsConnected (((↑) : ℂ → Sphere) '' E) :=
    (isConnected_complex_exterior_closedBall_center c hR).image _
      OnePoint.continuous_coe.continuousOn
  have hInf : (∞ : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' E) :=
    infty_mem_closure_image_of_unbounded (unbounded_complex_exterior c R)
  apply hE.subset_closure
  · rintro p ⟨z, hz, rfl⟩
    simpa [E, OnePoint.coe_injective.mem_set_image] using hz
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact hInf
    | coe z =>
      apply subset_closure
      exact mem_image_of_mem _ (by simpa [E, OnePoint.coe_injective.mem_set_image] using hp)

theorem isConnected_sphere_exterior_ball (c : ℂ) {R : ℝ} (hR : 0 < R) :
    IsConnected ((((↑) : ℂ → Sphere) '' ball c R)ᶜ) := by
  have hE : IsConnected (ball c R)ᶜ := by
    have hc := (isConnected_complex_exterior_closedBall_center c hR.le).closure
    simpa only [closure_compl, interior_closedBall c hR.ne'] using hc
  have hi : IsConnected (((↑) : ℂ → Sphere) '' (ball c R)ᶜ) :=
    hE.image _ OnePoint.continuous_coe.continuousOn
  have hu : ¬ Bornology.IsBounded (ball c R)ᶜ := fun h =>
    unbounded_complex_exterior c R (h.subset (compl_subset_compl.mpr ball_subset_closedBall))
  have hInf := infty_mem_closure_image_of_unbounded hu
  apply hi.subset_closure
  · rintro p ⟨z, hz, rfl⟩
    simpa [OnePoint.coe_injective.mem_set_image] using hz
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact hInf
    | coe z =>
      apply subset_closure
      exact mem_image_of_mem _ (by simpa [OnePoint.coe_injective.mem_set_image] using hp)

/-- A concrete sphere basis with compact containment and connected
complements. At finite points the neighborhoods are physical round disks;
at infinity they are exteriors of physical closed round disks. -/
theorem exists_sphere_neighborhood_connected_compl
    {W : Set Sphere} (hW : IsOpen W) {x : Sphere} (hx : x ∈ W) :
    ∃ V : Set Sphere, IsOpen V ∧ x ∈ V ∧ closure V ⊆ W ∧ IsConnected Vᶜ := by
  cases x using OnePoint.rec with
  | coe z =>
    have hn : ((↑) : ℂ → Sphere) ⁻¹' W ∈ 𝓝 z :=
      (hW.preimage OnePoint.continuous_coe).mem_nhds hx
    obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp hn
    let V : Set Sphere := ((↑) : ℂ → Sphere) '' ball z r
    have hcl : closure V = ((↑) : ℂ → Sphere) '' closedBall z r := by
      apply Set.Subset.antisymm
      · apply closure_minimal (image_mono ball_subset_closedBall)
        exact OnePoint.isClosed_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall _ _⟩
      · rw [← closure_ball z hr.ne']
        exact image_closure_subset_closure_image OnePoint.continuous_coe
    refine ⟨V, OnePoint.isOpen_image_coe.mpr isOpen_ball,
      mem_image_of_mem _ (mem_ball_self hr), ?_, isConnected_sphere_exterior_ball z hr⟩
    rw [hcl]
    rintro p ⟨w, hw, rfl⟩
    exact hball hw
  | infty =>
    have hc := (OnePoint.isOpen_iff_of_mem hx).mp hW
    obtain ⟨R, hR, hbound⟩ := hc.2.isBounded.exists_pos_norm_lt
    let V : Set Sphere := (((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) R)ᶜ
    let T : Set Sphere := (((↑) : ℂ → Sphere) '' ball (0 : ℂ) R)ᶜ
    have hV : IsOpen V :=
      (OnePoint.isClosed_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall _ _⟩).isOpen_compl
    have hT : IsClosed T := (OnePoint.isOpen_image_coe.mpr isOpen_ball).isClosed_compl
    have hVT : V ⊆ T := compl_subset_compl.mpr (image_mono ball_subset_closedBall)
    have hTW : T ⊆ W := by
      intro p hp
      cases p using OnePoint.rec with
      | infty => exact hx
      | coe z =>
        by_contra hzW
        have hzR := hbound z hzW
        apply hp
        exact mem_image_of_mem _ (by simpa using hzR)
    refine ⟨V, hV, OnePoint.infty_notMem_image_coe,
      (closure_minimal hVT hT).trans hTW, ?_⟩
    change IsConnected (((((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) R)ᶜ)ᶜ)
    rw [compl_compl]
    exact (Metric.isConnected_closedBall hR.le).image _ OnePoint.continuous_coe.continuousOn

end CircleDomainRigidity

end OAI
