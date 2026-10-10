import Mathlib
import OAI.Geometry.SplitTangent.EmbeddedHolomorphicAtlas
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.HolomorphicLocalDiffeomorph
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Product Criteria. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent

 
theorem injective_mfderiv_of_leftInverse {X Y : ComplexManifold.{u}}
    {i : Y.Carrier → X.Carrier} {p : X.Carrier → Y.Carrier}
    (hi : ContMDiff (ModelWithCorners Y) (ModelWithCorners X) ω i)
    (hp : ContMDiff (ModelWithCorners X) (ModelWithCorners Y) ω p)
    (hpi : Function.LeftInverse p i) (y : Y.Carrier) :
    Function.Injective (mfderiv (ModelWithCorners Y) (ModelWithCorners X) i y) := by
  have he : p ∘ i = id := funext hpi
  have hd := mfderiv_comp y ((hp (i y)).mdifferentiableAt (by simp))
    ((hi y).mdifferentiableAt (by simp))
  rw [he, mfderiv_id] at hd
  intro v w hvw
  have h := congrArg (mfderiv (ModelWithCorners X) (ModelWithCorners Y) p (i y)) hvw
  have hdv := congrArg (fun L : Model Y →L[ℂ] Model Y => L v) hd
  have hdw := congrArg (fun L : Model Y →L[ℂ] Model Y => L w) hd
  exact hdv.trans (h.trans hdw.symm)

 

theorem isProjective_factors {X Y Z : ComplexManifold.{u}}
    [Nonempty X.Carrier] [CompactSpace X.Carrier]
    (e : ProjectiveEmbedding X)
    (f : Diffeomorph (ModelWithCorners X)
      ((ModelWithCorners Y).prod (ModelWithCorners Z)) X.Carrier
      (Y.Carrier × Z.Carrier) ω) : IsProjective Y ∧ IsProjective Z := by
  let yz := f (Classical.arbitrary X.Carrier)
  let p : X.Carrier → Y.Carrier := fun x => (f x).1
  let q : X.Carrier → Z.Carrier := fun x => (f x).2
  let i : Y.Carrier → X.Carrier := fun y => f.symm (y, yz.2)
  let j : Z.Carrier → X.Carrier := fun z => f.symm (yz.1, z)
  have hp : ContMDiff (ModelWithCorners X) (ModelWithCorners Y) ω p :=
    contMDiff_fst.comp f.contMDiff
  have hq : ContMDiff (ModelWithCorners X) (ModelWithCorners Z) ω q :=
    contMDiff_snd.comp f.contMDiff
  have hi : ContMDiff (ModelWithCorners Y) (ModelWithCorners X) ω i :=
    f.symm.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  have hj : ContMDiff (ModelWithCorners Z) (ModelWithCorners X) ω j :=
    f.symm.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)
  have hpi : Function.LeftInverse p i := by intro y; simp [p, i]
  have hqj : Function.LeftInverse q j := by intro z; simp [q, j]
  have hpc : CompactSpace Y.Carrier :=
    hpi.surjective.compactSpace hp.continuous
  have hqc : CompactSpace Z.Carrier :=
    hqj.surjective.compactSpace hq.continuous
  exact ⟨⟨hpc, ⟨e.pullback i hi hpi.injective
    (injective_mfderiv_of_leftInverse hi hp hpi)⟩⟩,
    ⟨hqc, ⟨e.pullback j hj hqj.injective
    (injective_mfderiv_of_leftInverse hj hq hqj)⟩⟩⟩

namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem compatible_product_of_bijective_quotients [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
    (e : ProjectiveEmbedding X) (Y Z : ComplexManifold.{u})
    (q₁ : X.Carrier → Y.Carrier) (q₂ : X.Carrier → Z.Carrier)
    (hq₁ : ContMDiff (ModelWithCorners X) (ModelWithCorners Y) ω q₁)
    (hq₂ : ContMDiff (ModelWithCorners X) (ModelWithCorners Z) ω q₂)
    (hs₁ : ∀x, Function.Surjective (mfderiv (ModelWithCorners X) (ModelWithCorners Y) q₁ x))
    (hs₂ : ∀x, Function.Surjective (mfderiv (ModelWithCorners X) (ModelWithCorners Z) q₂ x))
    (hk₁ : ∀x, LinearMap.ker (mfderiv (ModelWithCorners X) (ModelWithCorners Y) q₁ x).toLinearMap=
      S.second x)
    (hk₂ : ∀x, LinearMap.ker (mfderiv (ModelWithCorners X) (ModelWithCorners Z) q₂ x).toLinearMap=
      S.first x)
    (hpair : Function.Bijective (fun x => (q₁ x,q₂ x))) : HasCompatibleProjectiveProduct X S := by
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
  let : LocallyPathConnectedSpace Y.Carrier := ChartedSpace.locallyPathConnectedSpace (Model Y) Y.Carrier
  let : LocallyPathConnectedSpace Z.Carrier := ChartedSpace.locallyPathConnectedSpace (Model Z) Z.Carrier
  have hl : IsLocalDiffeomorph (ModelWithCorners X) I ω q := by
    intro x
    have hI : I=𝓘(ℂ,Model Y × Model Z) := modelWithCornersSelf_prod.symm
    rw [hI] at hq hb ⊢
    exact HolomorphicLocalDiffeomorph.manifold_ift (hq x) (hb x)
  let f : Diffeomorph (ModelWithCorners X) I X.Carrier (Y.Carrier × Z.Carrier) ω :=
    hl.diffeomorphOfBijective hpair
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
