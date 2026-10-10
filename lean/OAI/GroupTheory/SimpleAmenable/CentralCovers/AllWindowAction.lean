import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.RectangularBound

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AllWindowAction
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem all_window_action_comparison (hlarge : 20 ≤ m+1)
    (h : ∀ n, B.CoordinateWindowLaw n)
    (k : Fin 3 → ℕ) (p : Fin 3 → Fin 2 → ℤ) (V : Fin 3 → polygonAlgebra a)
    (hV : ∀ i, ResolvedBy (fun t => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives (k i) (p i)) t).val) (V i).val)
    (he : V 0 ⊓ V 2 = V 1 ⊓ V 2)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) (k 2) (h (k 2)) (p 2) (V 2)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.windowSector (by omega) (k 0) (h (k 0)) (p 0) (V 0)
          (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.windowSector (by omega) (k 0) (h (k 0)) (p 0) (V 0)
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.windowSector (by omega) (k 1) (h (k 1)) (p 1) (V 1)
          (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.windowSector (by omega) (k 1) (h (k 1)) (p 1) (V 1)
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  obtain ⟨n,q,hq⟩ := finite_coordinate_windows_container k p
  have heq i : B.windowSector (by omega) (k i) (h (k i)) (p i) (V i) =
      B.windowSector (by omega) n (h n) q (V i) :=
    B.windowSector_inclusion (by omega) n (k i) (h n) (h (k i)) q (p i)
      (fun j => (hq i j).1) (fun j => (hq i j).2) (V i) (hV i)
  have hres i : ResolvedBy (fun t => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) t).val) (V i).val := by
    intro x y hxy
    apply hV i x y
    intro t
    have ht := hxy (coordinateWindowEmbedding n (k i) q (p i)
      (fun j => (hq i j).1) (fun j => (hq i j).2) t)
    have hs := congrFun (coordinateWindowEmbedding_spec n (k i) q (p i)
      (fun j => (hq i j).1) (fun j => (hq i j).2)) t
    dsimp only [Function.comp_def] at hs
    simpa only [primitiveTests,primitiveFamilyTests,hs] using ht
  rw [heq 2] at hc
  rw [heq 0,heq 1]
  exact B.chart_action_transfer hlarge (coordinateWindowPrimitives n q)
    (fun I _ b hb => h n I b hb q) (V 0) (V 1) (V 2)
    (hres 0) (hres 1) (hres 2) he f hf hc I s

end InitialCoverSystem
end AllWindowAction

end SimpleAmenable
end
end

end OAI
