import Mathlib
import OAI.Analysis.AffineBernstein.ConstantDet
import OAI.Analysis.AffineBernstein.DirectionalJacobi
import OAI.Analysis.AffineBernstein.HessianTraceIntegral

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedHessianUpper

lemma inverseNthRoot_sublevel_second {n : ℕ} (hn : 1 ≤ n) {f : Space n → ℝ}
    (hf : ∀ x, 0 < f x) {a x : Space n}
    (h : inverseNthRoot n f x ≤ 2*inverseNthRoot n f a) : f a ≤ (2:ℝ)^n*f x := by
  have H := pow_le_pow_left₀ (inverseNthRoot_pos f x).le h n
  rw [mul_pow,inverseNthRoot_pow hn (hf x),inverseNthRoot_pow hn (hf a)] at H
  have H' := mul_le_mul_of_nonneg_left H (mul_pos (hf a) (hf x)).le
  have he : f a*f x*(f x)⁻¹ = f a  := by field_simp [(hf x).ne', (hf a).ne']
  have he' : f a*f x*((2:ℝ)^n*(f a)⁻¹)=(2:ℝ)^n*f x  := by field_simp [(hf x).ne', (hf a).ne']
  rwa [he,he'] at H'

lemma hessian_diagonal_le_trace {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (i : Fin n) : hessian u x i i ≤ (hessian u x).trace := by
  exact Finset.single_le_sum (f := fun j => hessian u x j j)
    (fun _ _ => hp.posSemidef.diag_nonneg) (Finset.mem_univ i)

/-- A genuine normalized Hessian upper bound made from the original equation:
the inverse-root Jacobi supersolution, ABP critical density, and the shifted
gradient area formula. No interior regularity theorem is postulated. -/
theorem normalized_hessian_diagonal_upper {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ), ∀ i : Fin n, hessian v a i i ≤ C := by
  obtain ⟨δ,hδ,Hδ⟩ := normalized_critical_density hn hρ hρ1 hR
  let J := (n:ℝ)*(volume (Metric.closedBall (0:Space n) (4+(1/16:ℝ)))).toReal
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨(2:ℝ)^n*J/δ+1,by positivity,?_⟩
  intro v hv a ha i
  let f := fun x => hessian v x i i
  let s := inverseNthRoot n f
  have hne : coordinateVector n i ≠ 0 := by
    intro H
    have HH := congrArg (fun e : Space n => e i) H
    simp [coordinateVector] at HH
  have hf : ContDiff ℝ ∞ f := contDiff_dirDeriv (contDiff_dirDeriv hv.smooth _) _
  have hfp (x : Space n) : 0 < f x := by
    change 0 < dirDeriv (coordinateVector n i) (dirDeriv (coordinateVector n i) v) x
    rw [dirDeriv_eq_second hv.smooth.contDiffAt]
    exact second_fderiv_pos hv.smooth.contDiffAt (hv.posDef x) hne
  have hs : ContDiff ℝ ∞ s := contDiff_inverseNthRoot hf hfp
  have hsp (x : Space n) : 0 < s x := inverseNthRoot_pos f x
  have hD := balanced_affineMaximal_constant_det hn hv.smooth hv.posDef hv.maximal hρ hρ1 hv.balance
  have hLs : ∀ x, inverseHessianTrace v s x ≤ 0 :=
    constant_det_directional_inverse_root_supersolution hn hv.smooth hv.posDef hD hne
  let K := Metric.closedBall (0:Space n) (1/16:ℝ)
  let T := {x | x ∈ K ∧ s x ≤ 2*s a}
  have hK : IsCompact K := isCompact_closedBall _ _
  have hT : IsCompact T := compact_sublevel_in_compact hK hs.continuous (2*s a)
  have hTK : T ⊆ K := fun _ hx => hx.1
  have hlow : δ ≤ (volume T).toReal := Hδ v hv s hs (fun x => (hsp x).le) hLs a ha (s a) (hsp a) le_rfl
  have hpoint (x : Space n) (hx : x ∈ T) : f a ≤ (2:ℝ)^n*(hessian v x).trace := by
    exact (inverseNthRoot_sublevel_second hn hfp hx.2).trans
      (mul_le_mul_of_nonneg_left (hessian_diagonal_le_trace (hv.posDef x) i) (by positivity))
  let : IsFiniteMeasure (volume.restrict T) := ⟨by simpa using hT.measure_lt_top (μ := volume)⟩
  have hiT : IntegrableOn (fun x => (hessian v x).trace) T volume :=
    ContinuousOn.integrableOn_compact hT (continuous_hessian_trace hv.smooth).continuousOn
  have hiK : IntegrableOn (fun x => (hessian v x).trace) K volume :=
    ContinuousOn.integrableOn_compact hK (continuous_hessian_trace hv.smooth).continuousOn
  have hInt := setIntegral_mono_on (integrable_const (f a)) (hiT.const_mul ((2:ℝ)^n))
    hT.measurableSet hpoint
  rw [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,integral_const_mul] at hInt
  have hmon : (∫ x in T, (hessian v x).trace) ≤ ∫ x in K, (hessian v x).trace :=
    setIntegral_mono_set hiK (Filter.Eventually.of_forall fun x => (hv.posDef x).posSemidef.trace_nonneg)
      (Filter.Eventually.of_forall hTK)
  have hupper : (∫ x in K, (hessian v x).trace) ≤ J := by
    apply integral_hessian_trace_le_ball hv.smooth hv.posDef hK
    · intro x hx
      have hxq : x ∈ Metric.closedBall (0:Space n) (1/4:ℝ) :=
        Metric.closedBall_subset_closedBall (by norm_num) hx
      simpa only [gradient,LinearIsometryEquiv.norm_map] using normalized_gradient_bound hv hxq
    · intro x hx
      simpa only [K,Metric.mem_closedBall,dist_zero_right] using hx
  have Hmul := mul_le_mul_of_nonneg_left (hmon.trans hupper) (show 0 ≤ (2:ℝ)^n by positivity)
  have Hδ := mul_le_mul_of_nonneg_right hlow (hfp a).le
  have Hbound : f a ≤ (2:ℝ)^n*J/δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  change f a ≤ _
  linarith

theorem normalized_hessian_trace_upper {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ), (hessian v a).trace ≤ C := by
  obtain ⟨C,hC,H⟩ := normalized_hessian_diagonal_upper hn hρ hρ1 hR
  refine ⟨(n:ℝ)*C,mul_pos (by exact_mod_cast hn) hC,?_⟩
  intro v hv a ha
  simpa only [Matrix.trace,Matrix.diag_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => H v hv a ha i)

end NormalizedHessianUpper


end
end AffineBernstein
end

end OAI
