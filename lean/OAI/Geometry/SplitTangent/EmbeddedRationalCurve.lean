import Mathlib
import OAI.Geometry.SplitTangent.EmbeddedHolomorphicAtlas
import OAI.Geometry.SplitTangent.EmbeddedTangentLift
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves

namespace OAI

/-! Embedded Rational Curve. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent.EmbeddedHolomorphicAtlas
variable {X : ComplexManifold.{u}} {r : ℕ} {Z : Set X.Carrier}
  (L : EmbeddedHolomorphicAtlas X r Z) (g : RationalCurve X)
  (hf : ∀z,g.finite z∈Z) (hi : ∀z,g.infinity z∈Z)

 
def rationalCurve : RationalCurve L.manifold where
  finite := fun z => ⟨g.finite z,hf z⟩
  infinity := fun z => ⟨g.infinity z,hi z⟩
  finite_holomorphic := L.holomorphic_lift g.finite_holomorphic hf
  infinity_holomorphic := L.holomorphic_lift g.infinity_holomorphic hi
  overlap := fun z hz => Subtype.ext (g.overlap z hz)

 

def rationalSection (σ : CurveTangentSection g) :
    letI := L.chartedSpace;
    letI := L.isManifold;
    (hσf : ∀z,σ.finite z∈LinearMap.range
      (show (Fin r → ℂ) →ₗ[ℂ] Tangent X (g.finite z) from
        (show (Fin r → ℂ) →L[ℂ] Tangent X (g.finite z) from
          mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X)
            (Subtype.val : Z → X.Carrier) (L.rationalCurve g hf hi |>.finite z)).toLinearMap)) →
    (hσi : ∀z,σ.infinity z∈LinearMap.range
      (show (Fin r → ℂ) →ₗ[ℂ] Tangent X (g.infinity z) from
        (show (Fin r → ℂ) →L[ℂ] Tangent X (g.infinity z) from
          mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X)
            (Subtype.val : Z → X.Carrier) (L.rationalCurve g hf hi |>.infinity z)).toLinearMap)) →
    CurveTangentSection (L.rationalCurve g hf hi) := by
  letI := L.chartedSpace
  letI := L.isManifold
  intro hσf hσi
  exact {
    finite z := L.tangentLift ⟨g.finite z,hf z⟩ (σ.finite z)
    infinity z := L.tangentLift ⟨g.infinity z,hi z⟩ (σ.infinity z)
    finite_holomorphic := L.tangentLift_holomorphic σ.finite_holomorphic hσf
    infinity_holomorphic := L.tangentLift_holomorphic σ.infinity_holomorphic hσi
    overlap z hz := by
      have hh : (⟨g.finite z,hf z⟩ : Z)=⟨g.infinity z⁻¹,hi z⁻¹⟩ := Subtype.ext (g.overlap z hz)
      rw [hh,σ.overlap z hz] }

 

theorem rationalCurve_pointedGenerated
    (D : ∀x,Submodule ℂ (Tangent X x))
    (hg : PointedGenerated g D) :
    letI := L.chartedSpace;
    letI := L.isManifold;
    (hD : ∀y : Z, LinearMap.range
      (mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X)
        (Subtype.val : Z → X.Carrier) y).toLinearMap=D y.val) →
    PointedGenerated (L.rationalCurve g hf hi) (fun _ => ⊤) := by
  let := L.chartedSpace
  let := L.isManifold
  intro hD w hw
  let k := L.rationalCurve g hf hi
  let d := mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X)
    (Subtype.val : Z → X.Carrier) (k.finite 1)
  have hv : d w∈D (g.finite 1) := by
    change d w∈D ((k.finite 1 : Z).val)
    rw [←hD (k.finite 1)]
    exact ⟨w,rfl⟩
  obtain ⟨σ,hσf,hσi,hσ0,hσ1⟩ := hg (d w) hv
  have hf' z : σ.finite z∈LinearMap.range
      (show (Fin r → ℂ) →ₗ[ℂ] Tangent X (g.finite z) from
        (show (Fin r → ℂ) →L[ℂ] Tangent X (g.finite z) from
          mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X)
            (Subtype.val : Z → X.Carrier) (k.finite z)).toLinearMap) := by
    erw [hD]
    exact hσf z
  have hi' z : σ.infinity z∈LinearMap.range
      (show (Fin r → ℂ) →ₗ[ℂ] Tangent X (g.infinity z) from
        (show (Fin r → ℂ) →L[ℂ] Tangent X (g.infinity z) from
          mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X)
            (Subtype.val : Z → X.Carrier) (k.infinity z)).toLinearMap) := by
    erw [hD]
    exact hσi z
  refine ⟨L.rationalSection g hf hi σ hf' hi',fun _ => Submodule.mem_top,
    fun _ => Submodule.mem_top,?_,?_⟩
  · change L.tangentLift _ (σ.finite 0)=0
    rw [hσ0,map_zero]
  · change L.tangentLift _ (σ.finite 1)=w
    rw [hσ1]
    exact DFunLike.congr_fun (L.tangentLift_leftInverse (k.finite 1)) w

end SplitTangent.EmbeddedHolomorphicAtlas

end

end OAI
