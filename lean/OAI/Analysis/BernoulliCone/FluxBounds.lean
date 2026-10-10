import OAI.Analysis.BernoulliCone.CalibrationTraces

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
open Axisymmetric
lemma cap_positive_bounded {x:Space 7} (hq:Cylindrical.radiusSq axis x≤1)
    (hp:0<smoothCap x) : ‖x‖≤2 := by
  have hq0:=Cylindrical.radiusSq_nonneg axis x axis_norm
  obtain ⟨hv,hv1⟩:=CapAlgebra.V_bounds hq0 hq capB_bounds.1 capB_bounds.2
  have hy:=CapAlgebra.Y_pos hq0 hv capC_pos
  have hH:0<capH (Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB):=by
    change 0<CapAlgebra.Y _ _ _ * capH (_ * (CapAlgebra.V _ _)⁻¹) at hp
    rw [←div_eq_mul_inv] at hp
    exact pos_of_mul_pos_right hp hy.le
  have ha:|Cylindrical.axis axis x|<3/4:=by
    have hh:=(capH_pos_iff _).mp hH
    rw [abs_div,abs_of_pos hv,div_lt_iff₀ hv] at hh
    nlinarith
  have hsq:(Cylindrical.axis axis x)^2<(3/4:ℝ)^2:=by
    rw [←sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).mpr ha
  unfold Cylindrical.radiusSq at hq
  nlinarith [norm_nonneg x]
lemma cap_gradient_uniform_bound : ∃C:ℝ,0<C ∧
    ∀x:Space 7,Cylindrical.radiusSq axis x≤1 → 0<smoothCap x → ‖gradient smoothCap x‖≤C := by
  let S:Set (Space 7):={x|Cylindrical.radiusSq axis x≤1} ∩ Metric.closedBall 0 2
  have hs:IsCompact S:=(isCompact_closedBall (0:Space 7) 2).inter_left
    (isClosed_le (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous continuous_const)
  have hg:ContinuousOn (gradient smoothCap) S:=by
    intro x hx
    have hh:ContDiffAt ℝ ∞ (gradient smoothCap) x:=
      (toDual ℝ (Space 7)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x
        ((smoothCap_contDiffAt hx.1).fderiv_right (by simp))
    exact hh.continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩:=hs.exists_bound_of_continuousOn hg
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hq hp
  have hx:x∈S:=⟨hq,by simpa using cap_positive_bounded hq hp⟩
  exact (hC x hx).trans (by linarith [le_abs_self C])
lemma polarGradient_norm_bound {x:Space 7} (hx:x≠0) (a b:ℝ) :
    ‖polarGradient axis x a b‖≤|a|+|b| := by
  have hh:=norm_sq_polarGradient axis_norm hx a b
  have hab:0≤|a| * |b|:=mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb:0≤(inner ℝ x axis/‖x‖)^2*b^2:=mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith [sq_abs a,sq_abs b,norm_nonneg (polarGradient axis x a b),abs_nonneg a,abs_nonneg b]
lemma outer_gradient_uniform_bound : ∃C:ℝ,0<C ∧
    ∀x:Space 7,1≤Cylindrical.radiusSq axis x → 0<outerSigned x → ‖gradient outerSigned x‖≤C := by
  let R:ℝ→ℝ:=fun t=>|f t|+|fp t|+capAmplitude*(2*|gSup t|+|gSup1 t|)
  have hR:ContinuousOn R (Icc (-3/5:ℝ) (3/5)):=by
    intro t ht
    have ht1:t∈Ioo (-1:ℝ) 1:=⟨by linarith [ht.1],by linarith [ht.2]⟩
    have ht2:|t|<1:=abs_lt.mpr ht1
    exact (((hasDerivAt_f ht1).continuousAt.abs.add (hasDerivAt_fp ht1).continuousAt.abs).add
      (continuousAt_const.mul (((hasDerivAt_gSup ht2).continuousAt.abs.const_mul 2).add
        (hasDerivAt_gSup1 ht2).continuousAt.abs))).continuousWithinAt
  obtain ⟨C,hC⟩:=isCompact_Icc.exists_bound_of_continuousOn hR
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hq hp
  obtain ⟨hx,ha⟩:=radiusSq_pos_data (show 0<Cylindrical.radiusSq axis x by linarith)
  have hat:|angle x|≤3/5:=outer_nonnegative_angle hq hp.le
  have hn:1≤‖x‖:=by
    unfold Cylindrical.radiusSq at hq
    nlinarith [norm_nonneg x,sq_nonneg (Cylindrical.axis axis x)]
  have hn0:0<‖x‖:=by linarith
  have hfac:0≤‖x‖^(-2:ℝ)/‖x‖ ∧ ‖x‖^(-2:ℝ)/‖x‖≤1:=by
    rw [Real.rpow_neg (norm_nonneg x),Real.rpow_two]
    constructor
    · positivity
    · apply (div_le_one hn0).mpr
      exact (inv_le_one_of_one_le₀ (by nlinarith : 1≤‖x‖^2)).trans hn
  have hc:0≤capAmplitude*(‖x‖^(-2:ℝ)/‖x‖):=mul_nonneg capAmplitude_pos.le hfac.1
  have hc1:capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)≤capAmplitude:=by nlinarith [capAmplitude_pos]
  have hm:‖gradient outerSigned x‖≤R (angle x):=by
    rw [outerSigned_gradient hx ha]
    calc
      _≤‖polarGradient axis x (f (angle x)) (fp (angle x))‖+
          ‖(capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)) • polarGradient axis x (-2*gSup (angle x)) (gSup1 (angle x))‖ := norm_add_le _ _
      _≤(|f (angle x)|+|fp (angle x)|)+
          capAmplitude*(2*|gSup (angle x)|+|gSup1 (angle x)|) := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
        apply add_le_add (polarGradient_norm_bound hx _ _)
        have hh:=polarGradient_norm_bound hx (-2*gSup (angle x)) (gSup1 (angle x))
        norm_num only [abs_mul,abs_neg,abs_of_pos (by norm_num : 0<(2:ℝ))] at hh
        exact (mul_le_mul_of_nonneg_left hh hc).trans
          (mul_le_mul_of_nonneg_right hc1 (show 0≤2*|gSup (angle x)|+|gSup1 (angle x)| by positivity))
      _=R (angle x):=rfl
  have hbound:‖R (angle x)‖≤C:=hC _ (by simpa only [neg_div,Set.mem_Icc] using abs_le.mp hat)
  exact hm.trans ((le_abs_self _).trans (hbound.trans (by linarith [le_abs_self C])))
end Bernoulli.DeSilvaJerison

end
end

end OAI
