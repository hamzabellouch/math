import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.RectangularAtlas
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GridFormalPatching

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PrimitiveChartActions
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem primitive_coordinate_action (hlarge : 20 ≤ m+1)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (h' : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (i : ι) (i' : κ) (j j' : Fin 2) (u u' : CutRing × CutRing)
    (hp : P i=(coordinateTestIndex j,u)) (hp' : Q i'=(coordinateTestIndex j',u'))
    (V V' W : polygonAlgebra a)
    (hV : ResolvedBy (fun _ : Unit => (spatialTranslate u (coordinatePrimitive a j)).val) V.val)
    (hV' : ResolvedBy (fun _ : Unit => (spatialTranslate u' (coordinatePrimitive a j')).val) V'.val)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun s => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) s).val) W.val)
    (heq : V ⊓ W=V' ⊓ W)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.fullGeometricSector (by omega) P h V (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h V (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector (by omega) Q h' V' (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) Q h' V' (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  let S : Unit → Fin 5 × (CutRing × CutRing) := fun _ => (coordinateTestIndex j,u)
  let T : Unit → Fin 5 × (CutRing × CutRing) := fun _ => (coordinateTestIndex j',u')
  have hs := fun I (_ : I.card≤15) b hb => B.coordinateFamilyLaw_all g (fun _ : Unit => j) (fun _ => u) I b hb
  have ht := fun I (_ : I.card≤15) b hb => B.coordinateFamilyLaw_all g (fun _ : Unit => j') (fun _ => u') I b hb
  have h₀ := B.fullGeometricSector_shared_primitive (by omega) P S i () hp h hs V
    (by simpa only [primitiveTests,primitiveFamilyTests,hp,initialTest_coordinate] using hV)
  have h₁ := B.fullGeometricSector_shared_primitive (by omega) Q T i' () hp' h' ht V'
    (by simpa only [primitiveTests,primitiveFamilyTests,hp',initialTest_coordinate] using hV')
  rw [h₀,h₁]
  exact B.coordinate_charts_action hlarge g (fun _ : Unit => j) (fun _ => u)
    (fun _ : Unit => j') (fun _ => u') V V' W
    (by simpa only [primitiveTests,primitiveFamilyTests,initialTest_coordinate] using hV)
    (by simpa only [primitiveTests,primitiveFamilyTests,initialTest_coordinate] using hV')
    n q hW heq f hf hc I s

namespace RectangularAtlas
variable {B} (A : B.RectangularAtlas)

theorem slope_chart_eq (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (i : ι) (d : Fin 2) (z : CutRing × CutRing) (hp : P i=(slopeTestIndex d,z)) :
    A.slope hlarge d z=B.fullGeometricSector hlarge P h
      (spatialTranslate z (clippedSlopePrimitive a r (slopeDirection d))) := by
  unfold slope tangentSign
  simp only [↓reduceIte]
  apply B.fullGeometricSector_shared_primitive hlarge _ P (Sum.inl (0:Fin 2)) i
  · simpa only [translatedTemplate,tangentChartTemplate,ite_true,add_zero] using hp.symm
  · intro x y he
    have hh := he ()
    simpa only [primitiveTests,primitiveFamilyTests,translatedTemplate,tangentChartTemplate,
      ite_true,add_zero,initialTest_slope] using hh

end RectangularAtlas
end InitialCoverSystem
end PrimitiveChartActions

end SimpleAmenable
end
end

end OAI
