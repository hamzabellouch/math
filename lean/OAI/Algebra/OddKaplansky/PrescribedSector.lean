import OAI.Algebra.OddKaplansky.OrderedRectangles

namespace OAI

universe portUniverse1

section
namespace OddKaplansky.OrderedSourceSector
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier OrderedSectorOrbit
lemma T_leftFixed {H : Type portUniverse1} [Group H] [Fintype H] [LinearOrder H] (M : ℕ) [NeZero M] (r : Rep (H := H) M) :
    T M r = SectorStabilizer.stabilizer M (fun x => (lmb M r x).toAdd) := by
  ext g
  rw [mem_T]
  constructor
  · intro he x
    have hh := congrArg (fun a : Base (H := H) M => (a (g*x)).toAdd) he
    simpa only [shift_apply,inv_mul_cancel_left] using hh.symm
  · intro hg
    funext x
    apply Multiplicative.toAdd.injective
    have hh := hg (g⁻¹*x)
    simpa only [shift_apply,mul_inv_cancel_left] using hh.symm
end
end OddKaplansky.OrderedSourceSector

end

end OAI
