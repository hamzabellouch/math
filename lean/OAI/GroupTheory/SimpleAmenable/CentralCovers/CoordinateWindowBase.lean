import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.PrimitiveCovariance
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CoordinateWindowTarget

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CoordinateWindowBase

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem coordinateWindowLaw_of_zero (n : ℕ)
    (h : ∀ (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I),
      B.PrimitiveFamilyLaw I b hb (coordinateWindowPrimitives n 0)) :
    B.CoordinateWindowLaw n := by
  intro I b hb q
  let u : CutRing × CutRing := ((q 0 : CutRing)*cutTau,(q 1 : CutRing)*cutTau)
  have ht := PrimitiveFamilyLaw.translate B I b hb (coordinateWindowPrimitives n 0) (h I b hb) u
  apply PrimitiveFamilyLaw.congr_offsets B I b hb _ (coordinateWindowPrimitives n q) _ _ ht
  · intro i
    rfl
  · rintro ⟨j,i⟩
    simp only [coordinateWindowPrimitives,initialTest_coordinate]
    apply coordinatePrimitive_translate_eq
    fin_cases j <;> simp [u,coordinateShift,add_mul]

theorem CoordinateWindowLaw.mono {n k : ℕ} (h : B.CoordinateWindowLaw n) (hk : k ≤ n) :
    B.CoordinateWindowLaw k := by
  intro I b hb q
  let v : Fin 2 × Fin (k-1) → Fin 2 × Fin (n-1) :=
    fun i => (i.1,Fin.castLE (by omega) i.2)
  exact PrimitiveFamilyLaw.reindex B I b hb (coordinateWindowPrimitives n q) (h I b hb q) v

end InitialCoverSystem

theorem coordinateWindowLaw_eventually {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1) (n : ℕ) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
      B.CoordinateWindowLaw n := by
  classical
  let Z := Σ (I : Finset (Fin (m+1))), {b : Fin (m+1) // b ∉ I}
  have he (z : Z) := primitiveFamilyLaw_eventually (a := a) (hm := hm) hr hm' z.1 z.2.val z.2.property
    (coordinateWindowPrimitives n 0)
  choose L hL using he
  refine ⟨Finset.univ.sup L,fun M hM B => ?_⟩
  apply B.coordinateWindowLaw_of_zero n
  intro I b hb
  exact hL ⟨I,⟨b,hb⟩⟩ M ((Finset.le_sup (f := L) (Finset.mem_univ _)).trans hM) B

end CoordinateWindowBase

end SimpleAmenable
end
end

end OAI
