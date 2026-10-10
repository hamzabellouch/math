import OAI.Geometry.RCD.Sobolev.TimeUniformMean

namespace OAI

/-! # Continuous normalized affine residuals along actual paths -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

def pathAffineResidual (U : C(X,ℝ)) (r : ℝ) (γ : C(Time,X)) : C(Time,ℝ) :=
  r⁻¹ • (U.comp γ-
    ((U (γ 0)) • (1-⟨fun t : Time => (t:ℝ),continuous_subtype_val⟩)+
      (U (γ 1)) • ⟨fun t : Time => (t:ℝ),continuous_subtype_val⟩))

theorem pathAffineResidual_apply (U : C(X,ℝ)) (r : ℝ) (γ : C(Time,X)) (t : Time) :
    pathAffineResidual U r γ t=(U (γ t)-((1-(t:ℝ))*U (γ 0)+(t:ℝ)*U (γ 1)))/r := by
  simp only [pathAffineResidual,ContinuousMap.smul_apply,ContinuousMap.sub_apply,
    ContinuousMap.add_apply,ContinuousMap.comp_apply,ContinuousMap.one_apply,
    ContinuousMap.coe_mk,smul_eq_mul]
  ring

theorem pathAffineResidual_continuous (U : C(X,ℝ)) (r : ℝ) :
    Continuous (pathAffineResidual U r) := by
  let τ : C(Time,ℝ) := ⟨fun t => (t:ℝ),continuous_subtype_val⟩
  have h0 : Continuous (fun γ : C(Time,X) => U (γ 0)) :=
    U.continuous.comp (continuous_eval_const 0)
  have h1 : Continuous (fun γ : C(Time,X) => U (γ 1)) :=
    U.continuous.comp (continuous_eval_const 1)
  have hc : Continuous (fun γ : C(Time,X) =>
      U.comp γ-(U (γ 0) • (1-τ)+U (γ 1) • τ)) :=
    (ContinuousMap.continuous_postcomp U).sub
      ((h0.smul continuous_const).add (h1.smul continuous_const))
  exact hc.const_smul r⁻¹

theorem pathAffineResidual_norm_le (U : C(X,ℝ)) {r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    (hU : ∀ x, |U x| ≤ A) (γ : C(Time,X)) : ‖pathAffineResidual U r γ‖ ≤ 3*A/r := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  rw [Real.norm_eq_abs,pathAffineResidual_apply,abs_div,abs_of_pos hr]
  apply (div_le_div_iff_of_pos_right hr).mpr
  have h0 : |(1-(t:ℝ))*U (γ 0)| ≤ A := by
    rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr t.property.2)]
    exact (mul_le_mul_of_nonneg_left (hU _) (sub_nonneg.mpr t.property.2)).trans
      (mul_le_of_le_one_left hA (by linarith [t.property.1]))
  have h1 : |(t:ℝ)*U (γ 1)| ≤ A := by
    rw [abs_mul,abs_of_nonneg t.property.1]
    exact (mul_le_mul_of_nonneg_left (hU _) t.property.1).trans (mul_le_of_le_one_left hA t.property.2)
  have hb : |U (γ t)-((1-(t:ℝ))*U (γ 0)+(t:ℝ)*U (γ 1))| ≤
      |U (γ t)|+|(1-(t:ℝ))*U (γ 0)|+|(t:ℝ)*U (γ 1)| := by
    have hh := abs_sub_le (U (γ t)) 0 ((1-(t:ℝ))*U (γ 0)+(t:ℝ)*U (γ 1))
    simp only [sub_zero,zero_sub,abs_neg] at hh
    linarith [abs_add_le ((1-(t:ℝ))*U (γ 0)) ((t:ℝ)*U (γ 1))]
  linarith [hU (γ t)]

theorem pathAffineResidual_lipschitz (U : C(X,ℝ)) {r : ℝ} (hr : 0 < r)
    (γ : C(Time,X)) (hγ : IsGeodesic γ) {S : Set X} (hstay : ∀ t : Time, γ t∈S)
    {L D : ℝ≥0} (hU : LipschitzOnWith L U S)
    (hlen : dist (γ 0) (γ 1) ≤ (D:ℝ)*r) :
    LipschitzWith (2*L*D) (pathAffineResidual U r γ) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,pathAffineResidual_apply,pathAffineResidual_apply]
  have heq : (U (γ s)-((1-(s:ℝ))*U (γ 0)+(s:ℝ)*U (γ 1)))/r-
      (U (γ t)-((1-(t:ℝ))*U (γ 0)+(t:ℝ)*U (γ 1)))/r =
      ((U (γ s)-U (γ t))-((s:ℝ)-(t:ℝ))*(U (γ 1)-U (γ 0)))/r := by ring
  rw [heq,abs_div,abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  have hst : |U (γ s)-U (γ t)| ≤ (L:ℝ)*dist s t*dist (γ 0) (γ 1) := by
    have hh := hU.dist_le_mul (γ s) (hstay s) (γ t) (hstay t)
    rw [Real.dist_eq,hγ s t] at hh
    exact hh.trans_eq (by change _=(L:ℝ)*|(s:ℝ)-(t:ℝ)| * dist (γ 0) (γ 1); ring)
  have h01 : |U (γ 1)-U (γ 0)| ≤ (L:ℝ)*dist (γ 0) (γ 1) := by
    rw [abs_sub_comm]
    exact hU.dist_le_mul (γ 0) (hstay 0) (γ 1) (hstay 1)
  have ht : |((s:ℝ)-(t:ℝ))*(U (γ 1)-U (γ 0))| ≤
      dist s t*((L:ℝ)*dist (γ 0) (γ 1)) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h01 (abs_nonneg _)
  have htri := abs_sub_le (U (γ s)-U (γ t)) 0
    (((s:ℝ)-(t:ℝ))*(U (γ 1)-U (γ 0)))
  simp only [sub_zero,zero_sub,abs_neg] at htri
  have hlen' := mul_le_mul_of_nonneg_left hlen
    (mul_nonneg L.coe_nonneg (dist_nonneg (x := s) (y := t)))
  change _ ≤ (2*(L:ℝ)*(D:ℝ))*dist s t*r
  nlinarith

end RegularPointCoordinates

end

end OAI
