import OAI.Algebra.Finitistic.Dimension.PDResidueRing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

include k in
/-- The actual residue right module is semisimple. -/
theorem residue_semisimple : IsSemisimpleModule Aᵐᵒᵖ (Residue (A := A)) := by
  have : IsArtinianRing A := isArtinian_of_tower k inferInstance
  let S := A ⧸ Ring.jacobson A
  let q : A →+* S := Ideal.Quotient.mk (Ring.jacobson A)
  have : IsSemisimpleRing S := inferInstance
  have : IsSemisimpleRing Sᵐᵒᵖ := inferInstance
  have : RingHomSurjective q.op := ⟨fun s => by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective s.unop
    exact ⟨MulOpposite.op a, congrArg MulOpposite.op ha⟩⟩
  let f : A →ₛₗ[q.op] Sᵐᵒᵖ :=
    { toFun := fun a => MulOpposite.op (q a)
      map_add' := fun a b => by simp
      map_smul' := fun a b => by change MulOpposite.op (q (b*a.unop)) = _; simp }
  let e : Residue (A := A) →ₛₗ[q.op] Sᵐᵒᵖ :=
    (rightRadical (A := A)).liftQ f (by
      intro a ha
      change MulOpposite.op (Ideal.Quotient.mk (Ring.jacobson A) a) = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr ha, MulOpposite.op_zero])
  have hef : (fun s => e s) = (fun s : Residue (A := A) => MulOpposite.op (residueRingEquiv (k := k) s)) := by
    funext s
    induction s using Submodule.Quotient.induction_on with
    | _ a => rfl
  have he : Function.Bijective e := by
    change Function.Bijective (fun s => e s)
    rw [hef]
    exact MulOpposite.op_bijective.comp (residueRingEquiv (k := k)).bijective
  exact (e.isSemisimpleModule_iff_of_bijective he).mpr inferInstance
end LittleFinitistic.PDTensor

end

end OAI
