import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.HomogenizedPolynomialSection

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

include hΩ hcoord in
lemma polynomialInitial_delta_prescription (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base))
    (hdelta:∀m,polynomialSectionIncoming Ω C coord F m=if m=base then 1 else 0) :
    ∀d,sectionIncoming LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base d
      (polynomialInitial Ω C coord F)=coeff d (PowerSeries.C (Torus.X LaurentRay.vUnit Ω base)) := by
    intro d
    apply Finsupp.ext
    intro m
    by_cases hm:HasRootDegree C d (m-base)
    · rw [polynomialInitial_incoming Ω hΩ C coord hcoord base hb F hF d m hm,hdelta]
      by_cases he:m=base
      · subst m
        have H:=rootOrder_eq C coord hcoord hm
        rw [sub_self,map_zero] at H
        have hd:d=0:=by omega
        rw [hd]
        simp [Torus.X,Torus.monomial]
      · rw [ite_eq_right he,coeff_C]
        split_ifs <;> simp [Torus.X,Torus.monomial,Ne.symm he]
    · rw [sectionIncoming_apply,ite_eq_right hm]
      exact (ShiftGraded.monomial LaurentRay.vUnit Ω C base d m hm).symm

include hΩ hcoord in
lemma polynomialInitial_eq_theta (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base))
    (hdelta:∀m,polynomialSectionIncoming Ω C coord F m=if m=base then 1 else 0) :
    polynomialInitial Ω C coord F=thetaInitial LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base := by
  have hp:=polynomialInitial_delta_prescription Ω hΩ C coord hcoord base hb F hF hdelta
  let X:{X:PowerSeries (Torus LaurentRay.vUnit Ω) // ShiftGraded LaurentRay.vUnit Ω C base X}:=
    ⟨polynomialInitial Ω C coord F,polynomialInitial_graded Ω C coord hcoord base hb F hF⟩
  have U:=(existsUnique_section LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base
    (fun d=>coeff d (PowerSeries.C (Torus.X LaurentRay.vUnit Ω base)))
    (ShiftGraded.monomial LaurentRay.vUnit Ω C base))
  let Y:{X:PowerSeries (Torus LaurentRay.vUnit Ω) // ShiftGraded LaurentRay.vUnit Ω C base X}:=
    ⟨thetaInitial LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base,
      thetaInitial_graded LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base⟩
  have he:X=Y:=U.unique hp (thetaInitial_prescription LaurentRay.vUnit Ω C
    (simpleTotalTransport Ω C) base)
  exact congrArg Subtype.val he

include hΩ hcoord in
lemma polynomialSection_eq_thetaValue (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base))
    (hdelta:∀m,polynomialSectionIncoming Ω C coord F m=if m=base then 1 else 0)
    (h:M →+ ℝ) :
    adjoint (rootSectionChart Ω C h).val (homogenize LaurentRay.vUnit Ω (rootOrder coord) F)=
      thetaValue LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base h := by
  rw [rootSectionChart_action]
  change sectionValue _ _ _ _ _ (polynomialInitial Ω C coord F)=_
  rw [polynomialInitial_eq_theta Ω hΩ C coord hcoord base hb F hF hdelta]
  rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
