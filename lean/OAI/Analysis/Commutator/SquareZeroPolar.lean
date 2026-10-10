import Mathlib
import OAI.Analysis.Commutator.PartialIsometryOrder
import OAI.Analysis.Commutator.PolarSupport

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma partialIsometry_square_zero (T : H →L[ℂ] H) (hT : T*T=0) :
    partialIsometry T*partialIsometry T=0 := by
  let K : Submodule ℂ H := LinearMap.ker T.toLinearMap
  let : CompleteSpace K := T.isClosed_ker.completeSpace_coe
  let e : H →L[ℂ] H := K.starProjection
  have he : IsStarProjection e := isStarProjection_starProjection
  have heT : e*T=T := by
    ext x
    apply Submodule.starProjection_eq_self_iff.mpr
    exact congrArg (fun R : H →L[ℂ] H => R x) hT
  have hTe : T*e=0 := by
    ext x
    exact K.starProjection_apply_mem x
  have hTcomp : T*(1-e)=T := by rw [mul_sub,mul_one,hTe,sub_zero]
  have hsource := rightSupport_le T (1-e) he.one_sub hTcomp
  have hes : e*partialIsometry T=partialIsometry T := mul_partialIsometry_of_mul T e heT
  have hP : (rightSupport T)*(1-e)=rightSupport T :=
    ((isProjection_rightSupport T).le_iff_mul_eq_left he.one_sub).mp hsource
  have hPe : rightSupport T*e=0 := by
    rw [mul_sub,mul_one] at hP
    exact sub_eq_self.mp hP
  have hse : partialIsometry T*e=0 := by
    calc
      _=(partialIsometry T*rightSupport T)*e := by rw [rightSupport,partialIsometry_mul_initial]
      _=0 := by rw [mul_assoc,hPe,mul_zero]
  calc
    _=partialIsometry T*(e*partialIsometry T) := by rw [hes]
    _=0 := by rw [←mul_assoc,hse,zero_mul]

end Kadison.Polar

namespace Kadison.PartialIsometryOrder.Link

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

lemma initial_mul_final_eq_zero (v : Link M e f) (hv : v.val*v.val=0) :
    v.initial*v.final=0 := by
  change (star v.val*v.val)*(v.val*star v.val)=0
  calc
    _=star v.val*(v.val*v.val)*star v.val := by noncomm_ring
    _=0 := by rw [hv,mul_zero,zero_mul]

lemma initial_mul_self_eq_zero (v : Link M e f) (hv : v.val*v.val=0) :
    v.initial*v.val=0 := by
  change (star v.val*v.val)*v.val=0
  rw [mul_assoc,hv,mul_zero]

lemma self_mul_final_eq_zero (v : Link M e f) (hv : v.val*v.val=0) :
    v.val*v.final=0 := by
  change v.val*(v.val*star v.val)=0
  rw [←mul_assoc,hv,zero_mul]

end Kadison.PartialIsometryOrder.Link

end

end
end

end OAI
