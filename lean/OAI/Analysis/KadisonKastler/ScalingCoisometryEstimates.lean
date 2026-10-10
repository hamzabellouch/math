import OAI.Analysis.KadisonKastler.StateScalingCoisometry
import OAI.Analysis.KadisonKastler.StateVectorNormComparison

namespace OAI

/-! # Reference-state estimates for a scaling coisometry -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H} {r : ℝ}

theorem coisometry_norm_le (v : Algebra M) (hv : v*star v=1) : ‖v‖ ≤ 1 := by
  have hn : ‖v*star v‖=‖v‖*‖v‖ := CStarRing.norm_self_mul_star
  rw [hv] at hn
  have h1 : ‖(1 : Algebra M)‖ ≤ 1 := by
    have he : ‖star (1 : Algebra M)*(1 : Algebra M)‖=
        ‖(1 : Algebra M)‖*‖(1 : Algebra M)‖ := CStarRing.norm_star_mul_self
    simp only [star_one,one_mul] at he
    nlinarith [norm_nonneg (1 : Algebra M)]
  nlinarith [norm_nonneg v]

theorem StateScales.coisometry_state (v : Algebra M) (hv : v*star v=1)
    (hs : StateScales M Ω r v.val) (a : Algebra M) :
    vectorFunctional Ω (star v*a*v)=(r : ℂ)*vectorFunctional Ω a := by
  have h := hs (star v*a).val (star v*a).property
  change vectorFunctional Ω ((star v*a)*v) =
    (r : ℂ)*vectorFunctional Ω (v*(star v*a)) at h
  rw [← mul_assoc v,hv,one_mul] at h
  exact h

theorem StateScales.coisometry_vector_norm_sq (v : Algebra M) (hv : v*star v=1)
    (hs : StateScales M Ω r v.val) (a : Algebra M) :
    ‖a.val (v.val Ω)‖^2=r*‖a.val Ω‖^2 := by
  have h := hs.coisometry_state v hv (star a*a)
  have he : star (a*v)*(a*v)=star v*(star a*a)*v := by
    simp only [star_mul,mul_assoc]
  rw [← he,vectorFunctional_star_mul_self,vectorFunctional_star_mul_self] at h
  have hh := congrArg Complex.re h
  simpa only [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re,
    MulMemClass.coe_mul,mul_apply_eq_comp] using hh

theorem StateScales.coisometry_commutator_bound (v : Algebra M) (hv : v*star v=1)
    (hs : StateScales M Ω r v.val) (hr1 : r ≤ 1)
    (a b : Algebra M) (hb : Commute b v) :
    ‖(a*v-v*a).val Ω‖ ≤ 2*‖(a-b).val Ω‖ := by
  have hvnorm : ‖v‖ ≤ 1 := coisometry_norm_le v hv
  have hright : ‖(a-b).val (v.val Ω)‖ ≤ ‖(a-b).val Ω‖ := by
    have hn := hs.coisometry_vector_norm_sq v hv (a-b)
    have hbnd : r*‖(a-b).val Ω‖^2 ≤ ‖(a-b).val Ω‖^2 :=
      mul_le_of_le_one_left (sq_nonneg _) hr1
    nlinarith [norm_nonneg ((a-b).val (v.val Ω)),norm_nonneg ((a-b).val Ω)]
  have hleft : ‖v.val ((a-b).val Ω)‖ ≤ ‖(a-b).val Ω‖ :=
    (v.val.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hvnorm)
  have he : a*v-v*a=(a-b)*v-v*(a-b) := by
    rw [sub_mul,mul_sub]
    have hc := hb.eq
    rw [hc]
    abel
  rw [he]
  change ‖(a-b).val (v.val Ω)-v.val ((a-b).val Ω)‖ ≤ 2*‖(a-b).val Ω‖
  exact (norm_sub_le _ _).trans (by linarith)

end

end KadisonKastler

end OAI
