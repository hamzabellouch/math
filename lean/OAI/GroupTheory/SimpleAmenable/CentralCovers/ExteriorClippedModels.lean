import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ActiveClippedModelActions
import OAI.GroupTheory.SimpleAmenable.CentralCovers.InitialGridActions
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ClippedGerms

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ExteriorClippedModels
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem exterior_clipped_model_action {ι : Type*} [Finite ι]
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ)
    (G : ClippedGerm a r (slopeDirection d) u z)
    {j : ι → Fin 4} {c : ι → CutRing} (T : A.geometry.InwardChart j c z)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : Fin 2 → ι) (slope : ι)
    (hlo : ∀ k, j (lo k)=axisDirection k ∧ c (lo k)=pointCoordinate G.offset k-r)
    (hhi : ∀ k, j (hi k)=axisDirection k ∧ c (hi k)=pointCoordinate G.offset k+r)
    (hs : j slope=slopeDirection d ∧ c slope=integralCutForm a (slopeDirection d) G.offset)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
      (spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))).val)
    (σ : Fin 2 × Bool → Bool) (hσ : ¬ ∀ k, σ (k,false)=false ∧ σ (k,true)=true)
    (cell : Fin 2 → Fin A.geometry.mesh)
    (hout : Disjoint (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell)
      (coordinateRectangle a (fun _ => -r) (fun _ => r)))
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun e => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) e).val) W.val)
    (hinc : W ≤
      A.geometry.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ)
    (hinitial : W ≤ spatialTranslate u (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell))
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (x : BoundedRelationCover M (alternatingGenerator a r m hm)) (hx : x ∈ f.range) :
    A.primitiveStar (by omega) (slopeTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s)*x*
      (A.primitiveStar (by omega) (slopeTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
      (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))) ())
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
        (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))) ())
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  rw [A.primitiveStar_slope]
  have hcomm := A.exterior_grid_action hlarge hr d u cell hout n q W hW hinitial f hf hc I s x hx
  have hconstant := B.cell_constant_action hlarge _ (A.concurrentLaw T.vertex T.offset) _ _
    (A.inward_model_resolved T _ ())
    (A.concurrent_coordinateGate_resolved T.vertex T.offset z Prod.fst G.axialCut σ) false
    (by rw [G.model_restrict_gate T hr hz₁ hz₂ lo hi slope hlo hhi hs hR σ,ite_eq_right hσ];
        exact bot_inf_eq _) f hf
    (A.coordinateGate_control hlarge T.vertex T.offset z Prod.fst G.axialCut σ n q _ hW hinc f hf hc) I s x hx
  simp only [Bool.false_eq_true,↓reduceIte,one_mul,inv_one,mul_one] at hconstant
  rw [hconstant,hcomm.eq,mul_assoc,mul_inv_cancel,mul_one]

end InitialCoverSystem.PatchAtlas
end ExteriorClippedModels

end SimpleAmenable
end
end

end OAI
