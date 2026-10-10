import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactRotationalTwist
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TransportedManifold

namespace OAI

/-! # The smooth group structure on an invariant rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  (α : K →* MulAut G) (τ : G →* K)
  (hinv : ∀ k g, τ (α k g) = τ g) [hτ : Fact (Continuous τ)]

attribute [local instance] semidirectProductTopology

/-- The atlas comes from the original group through the graph projection. -/
@[instance_reducible]
def rotationalTwistChartedSpace : ChartedSpace E (rotationalTwist α τ hinv) :=
  pullbackChartedSpace (rotationalTwistHomeomorph α τ hinv hτ.out)

local instance : ChartedSpace E (rotationalTwist α τ hinv) :=
  rotationalTwistChartedSpace α τ hinv

theorem rotationalTwist_isManifold : IsManifold (𝓘(ℝ,E)) ∞ (rotationalTwist α τ hinv) :=
  pullback_isManifold (rotationalTwistHomeomorph α τ hinv hτ.out)

omit [LieGroup (𝓘(ℝ,E)) ⊤ G] in
theorem contMDiff_rotationalTwistProjection :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (rotationalTwistHomeomorph α τ hinv hτ.out) :=
  contMDiff_pullback (rotationalTwistHomeomorph α τ hinv hτ.out)

omit [LieGroup (𝓘(ℝ,E)) ⊤ G] in
theorem contMDiff_rotationalTwistGraph :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (rotationalTwistHomeomorph α τ hinv hτ.out).symm :=
  contMDiff_pullback_symm (rotationalTwistHomeomorph α τ hinv hτ.out)

variable (hα : ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
  (fun p : G × G => α ((τ p.1)⁻¹) p.2))

include hα in
theorem contMDiff_rotationalTwistMul :
    ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (fun p : rotationalTwist α τ hinv × rotationalTwist α τ hinv => p.1 * p.2) := by
  let e := rotationalTwistHomeomorph α τ hinv hτ.out
  have he : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ e :=
    contMDiff_rotationalTwistProjection α τ hinv
  have hp := (he.comp contMDiff_fst).prodMk (he.comp contMDiff_snd)
  have hm := (he.comp contMDiff_fst).mul (hα.comp hp)
  have hh := (contMDiff_rotationalTwistGraph α τ hinv).comp hm
  apply hh.congr
  intro p
  apply e.injective
  change e (p.1 * p.2) = e (e.symm (e p.1 * α ((τ (e p.1))⁻¹) (e p.2)))
  rw [e.apply_symm_apply]
  change p.1.val.left * α p.1.val.right p.2.val.left =
    p.1.val.left * α ((τ p.1.val.left)⁻¹) p.2.val.left
  rw [p.1.property]

include hα in
theorem contMDiff_rotationalTwistInv :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (fun p : rotationalTwist α τ hinv => p⁻¹) := by
  let e := rotationalTwistHomeomorph α τ hinv hτ.out
  have he : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ e :=
    contMDiff_rotationalTwistProjection α τ hinv
  have hp := he.inv.prodMk he.inv
  have hh := (contMDiff_rotationalTwistGraph α τ hinv).comp (hα.comp hp)
  apply hh.congr
  intro p
  apply e.injective
  change e p⁻¹ = e (e.symm (α ((τ ((e p)⁻¹))⁻¹) ((e p)⁻¹)))
  rw [e.apply_symm_apply]
  change α p.val.right⁻¹ p.val.left⁻¹ = α ((τ p.val.left⁻¹)⁻¹) p.val.left⁻¹
  rw [p.property,map_inv]
  simp only [inv_inv,map_inv]

include hα in
/-- Smoothness of the action along the inverse character is sufficient for
both smooth group operations on the graph. -/
theorem rotationalTwistLieGroup : LieGroup (𝓘(ℝ,E)) ∞ (rotationalTwist α τ hinv) where
  __ := rotationalTwist_isManifold α τ hinv
  contMDiff_mul := contMDiff_rotationalTwistMul α τ hinv hα
  contMDiff_inv := contMDiff_rotationalTwistInv α τ hinv hα

end PolycyclicRecognition

end

end OAI
