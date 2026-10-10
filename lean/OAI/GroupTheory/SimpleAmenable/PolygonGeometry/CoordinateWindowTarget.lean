import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CommonTranslatedCopies
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveWords

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CoordinateWindowTarget

def coordinateTestIndex (j : Fin 2) : Fin 5 := ⟨j.val+1,by omega⟩

@[simp] theorem initialTest_coordinate (a : ℕ) (r : CutRing) (j : Fin 2) :
    initialTest a r (coordinateTestIndex j) = coordinatePrimitive a j := by
  fin_cases j <;> rfl

noncomputable def coordinateWindowPrimitives (n : ℕ) (q : Fin 2 → ℤ) :
    Fin 2 × Fin (n-1) → Fin 5 × (CutRing × CutRing) := fun i =>
  (coordinateTestIndex i.1,coordinateShift i.1 (((q i.1 + (i.2.val : ℤ)) : CutRing)*cutTau))

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

def CoordinateWindowLaw (n : ℕ) : Prop :=
  ∀ (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) (q : Fin 2 → ℤ),
    B.PrimitiveFamilyLaw I b hb (coordinateWindowPrimitives n q)

end InitialCoverSystem

theorem coordinatePrimitive_translate_eq {a : ℕ} (j : Fin 2)
    (u v : CutRing × CutRing) (h : (if j = 0 then u.1 else u.2) =
      (if j = 0 then v.1 else v.2)) :
    spatialTranslate u (coordinatePrimitive a j) = spatialTranslate v (coordinatePrimitive a j) := by
  apply Subtype.ext
  ext p
  fin_cases j
  · change u.1 = v.1 at h
    simp [spatialTranslate,coordinatePrimitive,halfPlane,cutForm,translate_val,h]
  · change u.2 = v.2 at h
    simp [spatialTranslate,coordinatePrimitive,halfPlane,cutForm,translate_val,h]

end CoordinateWindowTarget

end SimpleAmenable
end
end

end OAI
