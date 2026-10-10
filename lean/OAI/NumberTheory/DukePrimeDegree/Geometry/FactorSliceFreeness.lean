import OAI.NumberTheory.DukePrimeDegree.Geometry.FactorPivotCylinder
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductCoordinates

namespace OAI

/-! # A free remaining-group orbit separates the whole root transversal -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates n q.processed T) (g : G n) (k : Fin n)

theorem factorSlice_fiber_injective_of_free (s : UpperRootTransverse n × T)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v =
        Quotient.mk _ ((g*s.1.val)*C.base s.2) → v = 1) :
    Set.InjOn (fun z : C.factorPivotDomain q g k × ℝ =>
      rootQuotientParametrization q.distinct (C.factorSlice q g k z.1,z.2))
      ({z : C.factorPivotDomain q g k | z.val.1 = s} ×ˢ univ) := by
  have hi : Function.Injective (fun v : positiveRootGeneratedGroup q.remaining =>
      rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v.val) := by
    intro v w he
    have h := congrArg (fun x => rightAction x w.val⁻¹) he
    rw [rightAction_mul,rightAction_mul,mul_inv_cancel,rightAction_one] at h
    have h1 := hfree (v.val*w.val⁻¹)
      ((positiveRootGeneratedGroup _).mul_mem
        (positiveRootGeneratedGroup_mono Finset.sdiff_subset v.prop)
        ((positiveRootGeneratedGroup _).inv_mem
          (positiveRootGeneratedGroup_mono Finset.sdiff_subset w.prop))) h
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  rintro ⟨z,t⟩ ⟨hz,_⟩ ⟨w,u⟩ ⟨hw,_⟩ h
  change rootQuotientParametrization q.distinct (C.factorSlice q g k z,t) =
    rootQuotientParametrization q.distinct (C.factorSlice q g k w,u) at h
  change z.val.1 = s at hz
  change w.val.1 = s at hw
  rw [C.factorSlice_orbit q g k,C.factorSlice_orbit q g k] at h
  have he : q.remainingFactor (z.val.2,t-C.factorTime q g k z) =
      q.remainingFactor (w.val.2,u-C.factorTime q g k w) := by
    apply hi
    simpa only [q.remainingFactor_val,hz,hw,factorTime] using h
  have hp := q.remainingFactor.injective he
  have hzw : z=w := Subtype.ext (Prod.ext (hz.trans hw.symm) (congrArg Prod.fst hp))
  subst w
  have ht : t=u := by
    have H := congrArg Prod.snd hp
    exact sub_left_inj.mp H
  exact Prod.ext rfl ht

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
