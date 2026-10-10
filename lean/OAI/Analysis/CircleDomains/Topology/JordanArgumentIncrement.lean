import OAI.Analysis.CircleDomains.Sobolev.ArgumentCircleIntegral
import OAI.Analysis.CircleDomains.Selection.FixedCircuitExclusion

namespace OAI

/-! Signed Green fixes the argument increment of a regular Jordan curve.
The sign is chosen once, before the interior point. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma regular_jordan_argument_increment
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ) :
    ∃ e : ℝ, |e| = 1 ∧ ∀ z ∈ jordanInterior H,
      ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
        (∀ t, (v t : UnitAddCircle) = normalizedArgument (γ t-z)) ∧ v 1-v 0 = e := by
  obtain ⟨e, he, hG⟩ := hgreen H γ hγ
  refine ⟨e, he, ?_⟩
  intro z hz
  let O : Set ℂ := {w | w ≠ z}
  have hO : IsOpen O := isOpen_ne_fun continuous_id continuous_const
  have hu : SmoothCircleOn (centeredArgument z) O := smoothCircleOn_centeredArgument z
  have hγO : ∀ t, γ t ∈ O := by
    intro t heq
    have ht := hγ.mem_frontier t
    rw [frontier, (jordanInterior_isOpen H).interior_eq] at ht
    exact ht.2 (heq ▸ hz)
  obtain ⟨v, hv, hp⟩ := exists_smooth_real_circuit_lift hO hu hγ.smooth hγO
  refine ⟨v, hv, hp, ?_⟩
  obtain ⟨r, hr, hrH⟩ := nhds_basis_closedBall.mem_iff.mp ((jordanInterior_isOpen H).mem_nhds hz)
  have hcover : closure (jordanInterior H) \ ⋃ _i : Fin 1, ball z r ⊆ O := by
    intro w hw heq
    subst w
    exact hw.2 (mem_iUnion.mpr ⟨0, mem_ball_self hr⟩)
  have hc := contDiffOn_circleFDeriv hO hu
  have hformula := hG 1 (fun _ => z) (fun _ => r) (fun _ => hr)
    (fun i j hij => (hij (Subsingleton.elim _ _)).elim) (fun _ => hrH) O hO hcover
    (fun w => circleFDeriv (centeredArgument z) w 1)
    (fun w => circleFDeriv (centeredArgument z) w Complex.I)
    (hc.clm_apply contDiffOn_const) (hc.clm_apply contDiffOn_const)
  have hzero : (∫ w in jordanInterior H \ ⋃ _i : Fin 1, closedBall z r,
      fderiv ℝ (fun w => circleFDeriv (centeredArgument z) w Complex.I) w 1 -
        fderiv ℝ (fun w => circleFDeriv (centeredArgument z) w 1) w Complex.I) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro w hw
    have hwO : w ∈ O := hcover ⟨subset_closure hw.1, fun h => hw.2 (by
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact mem_iUnion.mpr ⟨i, ball_subset_closedBall hi⟩)⟩
    exact sub_eq_zero.mpr (circleFDeriv_closed_complex hO hu hwO)
  have hinner : planarFormIntegral (fun w => circleFDeriv (centeredArgument z) w 1)
      (fun w => circleFDeriv (centeredArgument z) w Complex.I) (unitCircleParam z r) = 1 := by
    simpa only [circleFormIntegral, show (fun _ : ℂ => (1 : ℝ)) = 1 from rfl, one_mul] using centeredArgument_round_integral z hr
  have houter : planarFormIntegral (fun w => circleFDeriv (centeredArgument z) w 1)
      (fun w => circleFDeriv (centeredArgument z) w Complex.I) γ = v 1-v 0 := by
    simpa only [circleFormIntegral, show (fun _ : ℂ => (1 : ℝ)) = 1 from rfl, one_mul] using
      circleFormIntegral_constant_weight hO hu (fun _ => 1) γ hγ.smooth hγO v
        hv.continuous hp 1 (fun _ _ => rfl)
  simp only [Fin.sum_univ_one, hinner, houter, hzero] at hformula
  rcases le_total 0 e with hp | hn
  · rw [abs_of_nonneg hp] at he
    rw [he] at hformula ⊢
    linarith
  · rw [abs_of_nonpos hn] at he
    have he' : e = -1 := by linarith
    rw [he'] at hformula ⊢
    linarith

end CircleDomainRigidity

end

end OAI
