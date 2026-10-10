import Mathlib
import OAI.Geometry.SplitTangent.CoveringProductBackend
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.HolomorphicLocalDiffeomorph
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.ProductCriteria

namespace OAI

/-! Global Products. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
namespace SplitTangent
universe u

 

def compact_analytic_diffeomorph {X Y : ComplexManifold.{u}}
    [CompactSpace X.Carrier] [ConnectedSpace X.Carrier] [SimplyConnectedSpace Y.Carrier]
    (f : X.Carrier → Y.Carrier)
    (hf : ContMDiff (ModelWithCorners X) (ModelWithCorners Y) ω f)
    (hb : ∀x, Function.Bijective (mfderiv (ModelWithCorners X) (ModelWithCorners Y) f x)) :
    Diffeomorph (ModelWithCorners X) (ModelWithCorners Y) X.Carrier Y.Carrier ω := by
  let : LocallyPathConnectedSpace Y.Carrier := ChartedSpace.locallyPathConnectedSpace (Model Y) Y.Carrier
  have hl : IsLocalDiffeomorph (ModelWithCorners X) (ModelWithCorners Y) ω f :=
    fun x => HolomorphicLocalDiffeomorph.manifold_ift (hf x) (hb x)
  exact hl.diffeomorphOfBijective
    (CoveringProductBackend.compact_local_homeomorph_bijective hl.isLocalHomeomorph)

namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem compatible_product_of_quotients [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
    (e : ProjectiveEmbedding X) (Y Z : ComplexManifold.{u})
    [SimplyConnectedSpace Y.Carrier] [SimplyConnectedSpace Z.Carrier]
    (q₁ : X.Carrier → Y.Carrier) (q₂ : X.Carrier → Z.Carrier)
    (hq₁ : ContMDiff (ModelWithCorners X) (ModelWithCorners Y) ω q₁)
    (hq₂ : ContMDiff (ModelWithCorners X) (ModelWithCorners Z) ω q₂)
    (hs₁ : ∀x, Function.Surjective (mfderiv (ModelWithCorners X) (ModelWithCorners Y) q₁ x))
    (hs₂ : ∀x, Function.Surjective (mfderiv (ModelWithCorners X) (ModelWithCorners Z) q₂ x))
    (hk₁ : ∀x, LinearMap.ker (mfderiv (ModelWithCorners X) (ModelWithCorners Y) q₁ x).toLinearMap=
      S.second x)
    (hk₂ : ∀x, LinearMap.ker (mfderiv (ModelWithCorners X) (ModelWithCorners Z) q₂ x).toLinearMap=
      S.first x) : HasCompatibleProjectiveProduct X S := by
  let : ChartedSpace (Model Y × Model Z) (Y.Carrier × Z.Carrier) :=
    prodChartedSpace (Model Y) Y.Carrier (Model Z) Z.Carrier
  let : IsManifold 𝓘(ℂ,Model Y × Model Z) ω (Y.Carrier × Z.Carrier) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod Y.Carrier Z.Carrier
  let q : X.Carrier → Y.Carrier × Z.Carrier := fun x => (q₁ x,q₂ x)
  let I := (ModelWithCorners Y).prod (ModelWithCorners Z)
  have hq : ContMDiff (ModelWithCorners X) I ω q := hq₁.prodMk hq₂
  have hd (x : X.Carrier) : mfderiv (ModelWithCorners X) I q x=
      (mfderiv (ModelWithCorners X) (ModelWithCorners Y) q₁ x).prod
      (mfderiv (ModelWithCorners X) (ModelWithCorners Z) q₂ x) :=
    mfderiv_prodMk ((hq₁ x).mdifferentiableAt (by simp)) ((hq₂ x).mdifferentiableAt (by simp))
  have hb (x : X.Carrier) : Function.Bijective (mfderiv (ModelWithCorners X) I q x) := by
    rw [hd]
    exact HolomorphicFrobenius.complementary_quotients_bijective
      (E := Model X) (F := Model Y) (G := Model Z) (S.projector x)
      (S.idempotent x) _ _ (hs₁ x) (hs₂ x) (hk₁ x) (hk₂ x)
  let : SimplyConnectedSpace (Y.Carrier × Z.Carrier) :=
    CoveringProductBackend.simplyConnected_product
  let : LocallyPathConnectedSpace Y.Carrier := ChartedSpace.locallyPathConnectedSpace (Model Y) Y.Carrier
  let : LocallyPathConnectedSpace Z.Carrier := ChartedSpace.locallyPathConnectedSpace (Model Z) Z.Carrier
  have hl : IsLocalDiffeomorph (ModelWithCorners X) I ω q := by
    intro x
    have hI : I=𝓘(ℂ,Model Y × Model Z) := modelWithCornersSelf_prod.symm
    rw [hI] at hq hb ⊢
    exact HolomorphicLocalDiffeomorph.manifold_ift (hq x) (hb x)
  let f : Diffeomorph (ModelWithCorners X) I X.Carrier (Y.Carrier × Z.Carrier) ω :=
    hl.diffeomorphOfBijective
      (CoveringProductBackend.compact_local_homeomorph_bijective hl.isLocalHomeomorph)
  have hf : (f : X.Carrier → Y.Carrier × Z.Carrier)=q := rfl
  obtain ⟨hY,hZ⟩ := isProjective_factors e f
  refine ⟨Y,Z,hY,hZ,f,?_⟩
  intro x
  change Submodule.map (mfderiv (ModelWithCorners X) I q x).toLinearMap (S.first x)=_ ∧
    Submodule.map (mfderiv (ModelWithCorners X) I q x).toLinearMap (S.second x)=_
  rw [hd]
  exact ⟨HolomorphicFrobenius.image_range_projector_of_quotients
    (E := Model X) (F := Model Y) (G := Model Z) (S.projector x)
    (S.idempotent x) _ _ (hs₁ x) (hk₁ x) (hk₂ x),
    HolomorphicFrobenius.image_kernel_projector_of_quotients
    (E := Model X) (F := Model Y) (G := Model Z) (S.projector x)
    (S.idempotent x) _ _ (hs₂ x) (hk₁ x) (hk₂ x)⟩

end TangentSplitting
end SplitTangent

end

end OAI
