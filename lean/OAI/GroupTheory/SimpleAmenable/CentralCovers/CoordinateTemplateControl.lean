import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SmallControlCalculus
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ControlCalculus
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GridFormalPatching

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CoordinateTemplateControl
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    {ι κ : Type*} [Finite ι] [Finite κ]

theorem coordinate_control_to_template (hlarge : 20 ≤ m+1)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (j : κ → Fin 2) (u : κ → CutRing × CutRing) (v : κ → ι)
    (hv : P ∘ v=fun i => (coordinateTestIndex (j i),u i))
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (fun i => (coordinateTestIndex (j i),u i)) i).val) V.val)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) W.val)
    (hinc : W ≤ V)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q W)) :
    SmallControlled B.c f (B.fullGeometricSector (by omega) P h V) := by
  let J : Sum κ (Fin 2 × Fin (n-1)) → Fin 2 := Sum.elim j Prod.fst
  let Z : Sum κ (Fin 2 × Fin (n-1)) → CutRing × CutRing :=
    Sum.elim u (fun i => (coordinateWindowPrimitives n q i).2)
  let Q := fun i => (coordinateTestIndex (J i),Z i)
  have hQ := fun I (_ : I.card ≤ 15) b hb => B.coordinateFamilyLaw_all g J Z I b hb
  have hj := fun I (_ : I.card ≤ 15) b hb => B.coordinateFamilyLaw_all g j u I b hb
  have h₀ := B.fullGeometricSector_subfamily (by omega) Q
    (fun i => (coordinateTestIndex (j i),u i)) Sum.inl rfl hQ hj V hV
  have h₁ := B.fullGeometricSector_subfamily (by omega) Q
    (coordinateWindowPrimitives n q) Sum.inr rfl hQ (fun I _ b hb => g n I b hb q) W hW
  have h₂ := B.fullGeometricSector_subfamily (by omega) P
    (fun i => (coordinateTestIndex (j i),u i)) v hv h hj V hV
  rw [← h₂, h₀]
  change SmallControlled B.c f (B.fullGeometricSector (by omega)
    (coordinateWindowPrimitives n q) (fun I _ b hb => g n I b hb q) W) at hc
  rw [h₁] at hc
  apply B.control_trans hlarge f _ _ hf ?_ hc
  · exact B.fullGeometricSector_small_control (by omega) Q hQ W V hinc
  · exact B.fullGeometricSector_supported (by omega) Q hQ V
      (fun x y he => hV x y (fun i => he (Sum.inl i)))

end InitialCoverSystem
end CoordinateTemplateControl

end SimpleAmenable
end
end

end OAI
