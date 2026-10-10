import OAI.Analysis.CircleDomains.Modulus.RealAnchoredBarriers
import OAI.Analysis.CircleDomains.Topology.JordanFillLimits

namespace OAI

/-! The fixed round outer zero contour is an actual smooth source core. -/

open Set Function Filter Metric
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

def roundOuterJordan (R : ℝ) (hR : 0 < R) : ℂ ≃ₜ ℂ :=
  dilatedJordan (Homeomorph.refl ℂ) R hR

theorem roundOuterJordan_interior (R : ℝ) (hR : 0 < R) :
    jordanInterior (roundOuterJordan R hR) = ball 0 R := by
  simpa only [roundOuterJordan, Homeomorph.refl_apply, id_eq, image_id'] using
    jordanInterior_dilated (Homeomorph.refl ℂ) hR

abbrev roundOuterCore {G : Set Sphere} (R : ℝ) (hR : 0 < R)
    (hRG : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G) : SmoothJordanCore G where
  count := 1
  disk := fun _ => roundOuterJordan R hR
  curve := fun _ t => (R : ℂ) * (t : ℂ)
  disjoint := fun i j hij => (hij (Subsingleton.elim _ _)).elim
  subset_domain := by
    simpa only [closedJordanCore, roundOuterJordan_interior, iUnion_const] using hRG
  smooth := fun _ => by
    let : Fact (Module.finrank ℝ ℂ = 1 + 1) := Complex.finrank_real_complex_fact
    have hlin : ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ (fun z : ℂ => (R : ℂ) * z) :=
      (contDiff_const.mul contDiff_id).contMDiff
    exact hlin.comp contMDiff_coe_sphere
  embedding := fun _ =>
    (roundOuterJordan R hR).isEmbedding.comp (show Topology.IsEmbedding ((↑) : Circle → ℂ) from
      Topology.IsEmbedding.subtypeVal)
  boundary := fun _ => by
    rw [frontier_jordanInterior]
    change (roundOuterJordan R hR) '' sphere 0 1 = range (fun t : Circle => roundOuterJordan R hR t)
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩

namespace FiniteTransfer.RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem outer_region_subset_source :
    (((↑) : ℂ → Sphere) '' ball 0 (2 * M.radius))ᶜ ⊆ G :=
  (compl_subset_compl.mpr (image_mono (ball_subset_ball (by linarith [M.radius_pos])))).trans
    ((M.exterior_core 0).trans (M.core_source 0))

abbrev outerCore : SmoothJordanCore G :=
  roundOuterCore (2 * M.radius) (mul_pos (by norm_num) M.radius_pos) M.outer_region_subset_source

theorem outerCore_interior : jordanInterior (M.outerCore.disk 0) = ball 0 (2 * M.radius) :=
  roundOuterJordan_interior (2 * M.radius) (mul_pos (by norm_num) M.radius_pos)

theorem component_inside_outerCore (q : Sphere) :
    connectedComponentIn Gᶜ q ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (M.outerCore.disk 0) := by
  rw [M.outerCore_interior]
  intro p hp
  have hpG := connectedComponentIn_subset Gᶜ q hp
  have hpball : p ∈ ((↑) : ℂ → Sphere) '' ball 0 M.radius := by
    by_contra h
    exact hpG (M.core_source 0 (M.exterior_core 0 h))
  exact (image_mono (ball_subset_ball (by linarith [M.radius_pos]))) hpball

end FiniteTransfer.RealModelExhaustion

end CircleDomainRigidity

end

end OAI
