import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupEffectiveBound
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupIntersection
import OAI.AlgebraicGeometry.Seshadri.Intersection.PositiveSquareEffectivity
import OAI.AlgebraicGeometry.Seshadri.Blowup.NefPerturbation

namespace OAI


                                     
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.NefNumerics

theorem PointBlowup.boundaryNef_of_curve_bound (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (hr : 0 < r) {p : Configuration S r}
    (B : PointBlowup S r p)
    (hC : ∀ C : IntegralCurve S,
      Real.sqrt ((selfIntersection S L:ℝ)/r)*(totalMultiplicity S r C p:ℝ) ≤
        (curveDegree S L C:ℝ)) : B.BoundaryNef L := by
  classical
  let T := B.surface
  let P := L.pullback B.projection
  let H := selfIntersection S L
  let w := Real.sqrt ((H:ℝ)/r)
  have hH : 0 < H := S.selfIntersection_pos L hL
  have hHR : (0:ℝ) < H := by exact_mod_cast hH
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hw : 0 < w := Real.sqrt_pos.mpr (div_pos hHR hrR)
  have hvol : (H:ℝ) = (r:ℝ)*w^2 := by
    have hh : w^2 = (H:ℝ)/r := Real.sq_sqrt (div_nonneg hHR.le hrR.le)
    have he := (eq_div_iff (ne_of_gt hrR)).mp hh
    nlinarith only [he]
  obtain ⟨J,ι,hJ⟩ := B.isBlowup.1
  obtain ⟨hPP,hPJ,hc,hc0⟩ := S.blowup_intersections T L hL p B.projection
    B.overComplex B.isBlowup J ι hJ
  let c := selfIntersection T J
  obtain ⟨a,N,ha,hA'⟩ := B.isBlowup.eventual_ample_power_twist L hL J ι hJ
  obtain ⟨t,ht⟩ := exists_nat_gt (-(w*(c:ℝ))/(H:ℝ))
  let α := a*(max N t+1)
  let A := (P.pow α).tensor J
  have hA : A.IsAmple := hA' (max N t) (le_max_left _ _)
  have hα : t ≤ α := by dsimp [α]; nlinarith [le_max_right N t]
  have hpos : 0 < (α:ℝ)*H+w*c := by
    have ht' := (div_lt_iff₀ hHR).mp ht
    have hαR : (t:ℝ) ≤ α := by exact_mod_cast hα
    nlinarith only [ht',mul_le_mul_of_nonneg_right hαR hHR.le]
  intro C
  change 0 ≤ (curveDegree T P C:ℝ)+w*∑ i,(curveDegree T (B.exceptionalIdeal i) C:ℝ)
  rw [← Int.cast_sum,← B.total_ideal_degree S A hA J ι hJ C]
  by_contra hnot
  have hneg : (curveDegree T P C:ℝ)+w*curveDegree T J C < 0 := lt_of_not_ge hnot
  let u := curveDegree T P C
  let v := curveDegree T J C
  obtain ⟨I,τ,hI⟩ := C.invertible_ideal T
  have hPI : mixedEuler T P I = -u := C.ideal_mixed_degree T A hA I τ hI P
  have hJI : mixedEuler T J I = -v := C.ideal_mixed_degree T A hA I τ hI J
  obtain ⟨k,m,b,hk,hm,hb,hmk,hq,hample⟩ := negative_boundary_perturbation
    H c u v (selfIntersection T I) (α:ℤ) r w hH hr hw hvol hc hneg hpos
  let D := (P.pow k).tensor (J.pow m)
  let M := (D.pow 1).tensor (I.pow b)
  have hJP : mixedEuler T J P = 0 := by rw [mixedEuler_comm]; exact hPJ
  have hAP : mixedEuler T A P = (α:ℤ)*H := by
    change mixedEuler T ((P.pow α).tensor J) P = _
    rw [mixedEuler_tensor_left_general T A hA,mixedEuler_pow_left_general T A hA,
      mixedEuler_self,hPP,hJP]
    ring
  have hAJ : mixedEuler T A J = c := by
    change mixedEuler T ((P.pow α).tensor J) J = _
    rw [mixedEuler_tensor_left_general T A hA,mixedEuler_pow_left_general T A hA,
      hPJ,mixedEuler_self]
    ring
  have hAI : mixedEuler T A I = -((α:ℤ)*u+v) := by
    change mixedEuler T ((P.pow α).tensor J) I = _
    rw [mixedEuler_tensor_left_general T A hA,mixedEuler_pow_left_general T A hA,hPI,hJI]
    ring
  have hAD : mixedEuler T A D = (α:ℤ)*k*H+m*c := by
    change mixedEuler T A ((P.pow k).tensor (J.pow m)) = _
    rw [mixedEuler_tensor_right_general T A hA,mixedEuler_pow_right_general T A hA,
      mixedEuler_pow_right_general T A hA,hAP,hAJ]
    ring
  have hDI : mixedEuler T D I = -((k:ℤ)*u+(m:ℤ)*v) := by
    change mixedEuler T ((P.pow k).tensor (J.pow m)) I = _
    rw [mixedEuler_tensor_left_general T A hA,mixedEuler_pow_left_general T A hA,
      mixedEuler_pow_left_general T A hA,hPI,hJI]
    ring
  have hDD : selfIntersection T D = (k:ℤ)^2*H+(m:ℤ)^2*c := by
    change selfIntersection T ((P.pow k).tensor (J.pow m)) = _
    rw [T.selfIntersection_twist_general A hA,hPP,hPJ]
    ring
  have hMM : 0 < selfIntersection T M := by
    change 0 < selfIntersection T ((D.pow 1).tensor (I.pow b))
    rw [T.selfIntersection_twist_general A hA,hDD,hDI]
    convert hq using 1
    push_cast
    ring
  have hAM : 0 ≤ mixedEuler T A M := by
    change 0 ≤ mixedEuler T A ((D.pow 1).tensor (I.pow b))
    rw [mixedEuler_tensor_right_general T A hA,mixedEuler_pow_right_general T A hA,
      mixedEuler_pow_right_general T A hA,hAD,hAI]
    convert hample using 1
    push_cast
    ring
  obtain ⟨n,hn,hs⟩ := T.positive_square_eventually_effective A hA M hMM hAM
  obtain ⟨s,hs0⟩ := hs n le_rfl
  have hbound := @PointBlowup.effective_twist_bound S L hL r p B J ι hJ w hw.le hC
    I τ hI.1 k m b n hn s hs0
  have hlt := mul_lt_mul_of_pos_left hmk (mul_pos hw hrR)
  have hv := congrArg (fun z : ℝ => (k:ℝ)*z) hvol
  push_cast at hbound
  nlinarith only [hbound,hlt,hv]

end
end MaximalSeshadri.Geometry

end

end OAI
