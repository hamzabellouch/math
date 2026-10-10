import OAI.Analysis.CircleDomains.Topology.RecursiveComponentShrink
import OAI.Analysis.CircleDomains.Topology.FiniteComponentProjection
import OAI.Analysis.CircleDomains.Topology.SphereLevels

namespace OAI

/-! Sphere homeomorphisms shrinking the actual complementary components,
with simultaneous summable control of a component-constant observation. -/
open Set Function
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric

lemma exists_sphere_component_shrink
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hc : IsConnected G) (hi : ∞ ∈ G)
    {Z : Type*} [PseudoMetricSpace Z] (q : Sphere → Z) (hq : Continuous q)
    (hconstant : ∀ x ∈ Gᶜ, ∀ y ∈ connectedComponentIn Gᶜ x, q y=q x) :
    ∃ H : ℕ → (Sphere ≃ₜ Sphere),
      (∀ n, ∀ x ∈ Gᶜ, ∀ y ∈ connectedComponentIn Gᶜ x,
        dist (H n x) (H n y)<componentShrinkRadius n) ∧
      (∀ n x, dist (H (n+1) x) (H n x)<2*componentShrinkRadius n) ∧
      ∀ n x, dist (q ((H (n+1)).symm x)) (q ((H n).symm x))<componentShrinkRadius n := by
  let F := ((↑) : ℂ → Sphere) ⁻¹' Gᶜ
  have hF : IsCompact F := isCompact_finite_preimage hG.isClosed_compl (not_not.mpr hi)
  have hFc : IsConnected Fᶜ := finite_complement_connected hG hc hi
  have hconst : ∀ x ∈ F, ∀ y ∈ connectedComponentIn F x,
      q (y : Sphere)=q (x : Sphere) := by
    intro x hx y hy
    apply hconstant (x : Sphere) hx (y : Sphere)
    exact connectedComponentIn_mono _ (image_preimage_subset _ _)
      ((OnePoint.continuous_coe (X := ℂ)).continuousOn.image_connectedComponentIn_subset
        (s := F) hx (mem_image_of_mem _ hy))
  obtain ⟨H,hsmall,hforward,hinverse⟩ := exists_recursive_component_shrink
    hsard hsch hF hFc ((↑) : ℂ → Sphere) (fun z : ℂ => q (z : Sphere))
    OnePoint.continuous_coe (hq.comp OnePoint.continuous_coe) hconst
  refine ⟨fun n => (H n).onePointCongr,?_,?_,?_⟩
  · intro n x hx y hy
    have hyG := connectedComponentIn_subset _ _ hy
    cases x using OnePoint.rec with
    | infty => exact (hx hi).elim
    | coe a =>
      cases y using OnePoint.rec with
      | infty => exact (hyG hi).elim
      | coe b =>
        have hab := finite_component_membership hi hx hy
        have hm : H n b ∈ connectedComponentIn ((H n) '' F) (H n a) := by
          rw [← homeomorph_image_componentIn (H n) hx]
          exact mem_image_of_mem _ hab
        have hb := hsmall n (H n a) (mem_image_of_mem _ hx) (H n b) hm
        change dist ((H n a : ℂ) : Sphere) ((H n b : ℂ) : Sphere)<_
        rwa [dist_comm] at hb
  · intro n x
    cases x using OnePoint.rec with
    | infty => simpa using mul_pos (by norm_num : (0:ℝ)<2) (componentShrinkRadius_pos n)
    | coe a => exact hforward n a
  · intro n x
    cases x using OnePoint.rec with
    | infty => simpa using componentShrinkRadius_pos n
    | coe a => exact hinverse n a

end CircleDomainRigidity

end

end OAI
