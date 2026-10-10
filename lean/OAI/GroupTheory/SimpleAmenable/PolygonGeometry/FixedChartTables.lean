import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.PrimitiveCovariance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FixedChartTables

theorem fixedChartTables_eventually {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {η : Type*} [Finite η] {ι : η → Type*} [∀ z, Finite (ι z)]
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1)
    (P : (z : η) → ι z → Fin 5 × (CutRing × CutRing)) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
      ∀ z u I b hb, B.PrimitiveFamilyLaw I b hb (fun i => ((P z i).1,u+(P z i).2)) := by
  classical
  let Z := Σ (_ : η), Σ (I : Finset (Fin (m+1))), {b : Fin (m+1) // b ∉ I}
  have he (z : Z) := primitiveFamilyLaw_eventually (a := a) (hm := hm) hr hm'
    z.2.1 z.2.2.val z.2.2.property (P z.1)
  choose L hL using he
  let _ := Fintype.ofFinite Z
  refine ⟨Finset.univ.sup L,fun M hM B z u I b hb => ?_⟩
  apply InitialCoverSystem.PrimitiveFamilyLaw.translate B I b hb (P z) _ u
  exact hL ⟨z,I,⟨b,hb⟩⟩ M ((Finset.le_sup (f := L) (Finset.mem_univ _)).trans hM) B
end FixedChartTables

end SimpleAmenable
end
end

end OAI
