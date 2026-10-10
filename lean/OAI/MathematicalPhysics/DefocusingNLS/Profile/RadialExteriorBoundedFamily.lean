import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorResidualLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorBoundedExpansion

namespace OAI

/-! Common real-tail extensions of the uniformly convergent polynomial families. -/

open Polynomial Set Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def radialExteriorTailVariable (T t : ℝ) : ℝ := Real.exp (-2*max t T)

theorem radialExteriorTailVariable_mem (T t : ℝ) :
    radialExteriorTailVariable T t ∈ Icc (0 : ℝ) (Real.exp (-2*T)) := by
  refine ⟨(Real.exp_pos _).le,Real.exp_le_exp.mpr ?_⟩
  nlinarith [le_max_right t T]

noncomputable def boundedRadialPolynomialAfter (T : ℝ) (P : ℂ[X]) : ℝ →ᵇ ℂ := by
  classical
  have hc : Continuous (fun x : ℝ => P.eval (x : ℂ)) := by fun_prop
  have hb := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (Real.exp (-2*T)))).exists_bound_of_continuousOn
    hc.continuousOn
  exact BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => P.eval (radialExteriorTailVariable T t : ℂ))
    (by unfold radialExteriorTailVariable; fun_prop) (Classical.choose hb)
    (fun t => Classical.choose_spec hb _ (radialExteriorTailVariable_mem T t))

theorem boundedRadialPolynomialAfter_apply (T : ℝ) (P : ℂ[X]) (t : ℝ) :
    boundedRadialPolynomialAfter T P t=P.eval (radialExteriorTailVariable T t : ℂ) := rfl

theorem boundedRadialPolynomialAfter_eq (T : ℝ) (P : ℂ[X]) (t : ℝ) (ht : T ≤ t) :
    boundedRadialPolynomialAfter T P t=radialExteriorPolynomialFunction P t := by
  simp only [boundedRadialPolynomialAfter_apply,radialExteriorTailVariable,max_eq_left ht,
    radialExteriorPolynomialFunction]

theorem boundedRadialPolynomialAfter_limit (T ε : ℝ) (hT : Real.exp (-2*T) ≤ ε)
    (P : ℕ → ℂ[X]) (Q : ℂ[X])
    (hP : TendstoUniformlyOn (fun n z => (P n).eval z) (fun z => Q.eval z)
      atTop (Metric.closedBall (0 : ℂ) ε)) :
    Tendsto (fun n => boundedRadialPolynomialAfter T (P n)) atTop
      (nhds (boundedRadialPolynomialAfter T Q)) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hP) (η/2) (by positivity)] with n hn
  rw [dist_eq_norm]
  have hb : ‖boundedRadialPolynomialAfter T (P n)-boundedRadialPolynomialAfter T Q‖ ≤ η/2 := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro t
    have hx := radialExteriorTailVariable_mem T t
    have hmem : (radialExteriorTailVariable T t : ℂ) ∈ Metric.closedBall (0 : ℂ) ε := by
      simp only [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg hx.1]
      exact hx.2.trans hT
    have he := (hn _ hmem).le
    rw [dist_comm,dist_eq_norm] at he
    exact he
  exact hb.trans_lt (by linarith)

noncomputable def boundedRadialResidualAfter (T : ℝ) (P : ℂ[X]) : ℝ →ᵇ ℂ × ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (0,-boundedRadialPolynomialAfter T P t))
    (continuous_const.prodMk (boundedRadialPolynomialAfter T P).continuous.neg)
    ‖boundedRadialPolynomialAfter T P‖ (fun t => by
      simp only [Prod.norm_def,norm_zero,norm_neg,max_eq_right (norm_nonneg _)]
      exact (boundedRadialPolynomialAfter T P).norm_coe_le_norm t)

theorem boundedRadialResidualAfter_apply (T : ℝ) (P : ℂ[X]) (t : ℝ) :
    boundedRadialResidualAfter T P t=(0,-boundedRadialPolynomialAfter T P t) := rfl

theorem boundedRadialResidualAfter_difference (T : ℝ) (P Q : ℂ[X]) :
    ‖boundedRadialResidualAfter T P-boundedRadialResidualAfter T Q‖ ≤
      ‖boundedRadialPolynomialAfter T P-boundedRadialPolynomialAfter T Q‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro t
  change ‖((0 : ℂ),-boundedRadialPolynomialAfter T P t)-
    ((0 : ℂ),-boundedRadialPolynomialAfter T Q t)‖ ≤ _
  simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,
    neg_sub_neg,norm_sub_rev,max_eq_right (norm_nonneg _)]
  exact (boundedRadialPolynomialAfter T P-boundedRadialPolynomialAfter T Q).norm_coe_le_norm t

theorem boundedRadialResidualAfter_limit (T ε : ℝ) (hT : Real.exp (-2*T) ≤ ε)
    (P : ℕ → ℂ[X]) (Q : ℂ[X])
    (hP : TendstoUniformlyOn (fun n z => (P n).eval z) (fun z => Q.eval z)
      atTop (Metric.closedBall (0 : ℂ) ε)) :
    Tendsto (fun n => boundedRadialResidualAfter T (P n)) atTop
      (nhds (boundedRadialResidualAfter T Q)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun n => boundedRadialResidualAfter_difference T (P n) Q))
  exact tendsto_iff_norm_sub_tendsto_zero.mp (boundedRadialPolynomialAfter_limit T ε hT P Q hP)

theorem boundedRadialResidualAfter_factor (T : ℝ) (P R : ℂ[X]) (j : ℕ)
    (hPR : P=X^j*R) (t : ℝ) (ht : T ≤ t) :
    Real.exp (-(2*(j : ℝ))*t) • boundedRadialResidualAfter T R t =
      (0,-radialExteriorPolynomialFunction P t) := by
  have he : radialExteriorPolynomialFunction P t=
      (Real.exp (-(2*(j : ℝ))*t) : ℂ)*radialExteriorPolynomialFunction R t := by
    simp only [radialExteriorPolynomialFunction,hPR,eval_mul,eval_pow,eval_X]
    congr 1
    rw [← Complex.ofReal_pow,← Real.exp_nat_mul]
    congr 2
    ring
  rw [he,boundedRadialResidualAfter_apply,boundedRadialPolynomialAfter_eq T R t ht]
  apply Prod.ext
  · simp
  · simp [Complex.real_smul]

theorem exists_radialExterior_bounded_residual_family (ν m : ℕ → ℂ) (ν₀ m₀ : ℂ)
    (hν : Tendsto ν atTop (nhds ν₀)) (hm : Tendsto m atTop (nhds m₀))
    (hm₀ : ‖m₀‖ < 1) (j : ℕ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ R : ℕ → ℂ[X], ∃ R₀ : ℂ[X],
      (∀ n, radialExteriorPolynomialResidual (ν n) n (radialExteriorExpansion (ν n) n (m n) j)=X^j*R n) ∧
      radialExteriorLinearResidual ν₀ (radialFreeExpansion ν₀ m₀ j)=X^j*R₀ ∧
      Tendsto (fun n => boundedRadialResidualAfter T (R n)) atTop
        (nhds (boundedRadialResidualAfter T R₀)) := by
  obtain ⟨ε,hε,_,R,R₀,hR,hR₀,hlim⟩ := radialExterior_normalized_residual_limit ν m ν₀ m₀ hν hm hm₀ j
  have hx : Tendsto (fun t : ℝ => Real.exp (-2*t)) atTop (nhds 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)) using 1
    funext t
    simp [neg_mul]
  obtain ⟨T,hT,hTe⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hx.eventually (gt_mem_nhds hε))).exists
  exact ⟨T,hT,R,R₀,hR,hR₀,boundedRadialResidualAfter_limit T ε hTe.le R R₀ hlim⟩

end DefocusingNLS

end OAI
