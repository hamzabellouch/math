import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

namespace ShearFlows
theorem spatial_fderiv_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : SpaceTime → E} (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (fun y : SpaceTime => fderiv ℝ (fun x => U (y.1, x)) y.2) := by
  have h : ContDiff ℝ ∞
      (Function.uncurry (fun y : SpaceTime => fun x : Space => U (y.1, x))) :=
    hU.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact h.fderiv contDiff_snd (by simp)

theorem timeDerivative_eq {V : Velocity} (hV : ContDiff ℝ ∞ V) (t : ℝ) (x : Space) :
    timeDerivative V t x = fderiv ℝ V (t, x) (1, 0) := by
  exact (((hV.differentiable (by simp) (t,x)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

theorem timeDerivative_smooth {V : Velocity} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun y : SpaceTime => timeDerivative V y.1 y.2) := by
  simp only [timeDerivative_eq hV]
  exact (hV.fderiv_right (by simp)).clm_apply contDiff_const

theorem initialTimeDerivative_eq {V : Velocity} (hV : ContDiff ℝ ∞ V)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    initialTimeDerivative V t x = timeDerivative V t x := by
  apply DifferentiableAt.derivWithin
  · exact ((hV.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)) t
  · exact uniqueDiffOn_Ici 0 t ht

theorem laplacian_smooth {V : Velocity} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun y : SpaceTime => laplacian (fun x => V (y.1, x)) y.2) := by
  apply ContDiff.sum
  intro j _
  have hj : ContDiff ℝ ∞
      (fun y : SpaceTime => derivative (fun x => V (y.1, x)) j y.2) :=
    (spatial_fderiv_smooth hV).clm_apply contDiff_const
  exact (spatial_fderiv_smooth hj).clm_apply contDiff_const

theorem force_smooth {V : Velocity} (hV : ContDiff ℝ ∞ V) (ν : ℝ) :
    ContDiff ℝ ∞ (force ν V) :=
  (timeDerivative_smooth hV).sub ((laplacian_smooth hV).const_smul ν)

theorem gradient_constant (c : ℝ) (x : Space) :
    ShearFlows.gradient (fun _ => c) x = 0 := by
  funext j
  change (fderiv ℝ (fun _ : Space => c) x) (basis j) = 0
  rw [fderiv_const_apply]
  rfl

theorem smooth_classicalRegularity {V : Velocity} (hV : ContDiff ℝ ∞ V) :
    ClassicalRegularity V (fun _ => 0) where
  spatial_u t _ := (hV.comp (contDiff_const.prodMk contDiff_id)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  temporal_u t _ x :=
    (((hV.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)) t).differentiableWithinAt
  spatial_p _ _ := contDiff_const
  continuous_u _ _ := hV.continuous.continuousOn
  continuous_du _ _ := (spatial_fderiv_smooth hV).continuous.continuousOn
  continuous_ddu _ _ :=
    (spatial_fderiv_smooth (spatial_fderiv_smooth hV)).continuous.continuousOn
  continuous_ut T _ :=
    (timeDerivative_smooth hV).continuous.continuousOn.congr (fun y hy =>
      initialTimeDerivative_eq hV hy.1.1 y.2)
  continuous_p _ _ := continuous_const.continuousOn
  continuous_dp _ _ := by
    simp only [gradient_constant]
    exact continuous_const.continuousOn

theorem velocity_solves_forced_NS {V : Velocity} {L : ℝ}
    (hV : ContDiff ℝ ∞ V) (hper : SpatiallyPeriodic L V)
    (hdiv : Solenoidal V) (hadv : ZeroAdvection V) (h₀ : ∀ x, V (0,x) = 0) (ν : ℝ) :
    IsClassicalSolution L ν (force ν V) V (fun _ => 0) where
  regularity := smooth_classicalRegularity hV
  periodic_u t _ := hper t
  periodic_p _ _ _ _ := rfl
  pressure_mean _ _ := by simp
  initial := h₀
  divergence_zero t _ := hdiv t
  equation t ht x := by
    rw [initialTimeDerivative_eq hV ht x, hadv t x]
    simp [force, gradient_constant]

theorem kineticEnergy_bound {V : Velocity} (hV : Continuous V) (L : ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, ‖V y‖ ≤ B) (t : ℝ) :
    kineticEnergy L V t ≤ (1 / 2 : ℝ) * volume.real (fundamentalCube L) * (3 * B^2) := by
  have hi : IntegrableOn (fun x : Space => ∑ j : Fin 3, (V (t,x) j)^2)
      (fundamentalCube L) := by
    apply Continuous.integrableOn_Icc
    apply continuous_finsetSum
    intro j _
    exact ((continuous_apply j).comp
      (hV.comp (continuous_const.prodMk continuous_id))).pow 2
  have hc : IntegrableOn (fun _ : Space => 3 * B^2) (fundamentalCube L) :=
    continuous_const.integrableOn_Icc
  have hp (x : Space) : (∑ j : Fin 3, (V (t,x) j)^2) ≤ 3 * B^2 := by
    calc
      (∑ j : Fin 3, (V (t,x) j)^2) ≤ ∑ _j : Fin 3, B^2 := by
        apply Finset.sum_le_sum
        intro j _
        have ha : |V (t,x) j| ≤ B := (norm_le_pi_norm _ j).trans (hb (t,x))
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).2 ha
      _ = 3 * B^2 := by simp
  have hint := setIntegral_mono_on hi hc measurableSet_Icc (fun x _ => hp x)
  simp only [setIntegral_const, smul_eq_mul] at hint
  unfold kineticEnergy
  nlinarith

theorem kineticEnergy_uniform_bound {V : Velocity} (hV : Continuous V)
    (hb : BoundedMixedDerivatives V) (L : ℝ) :
    ∃ B : ℝ, ∀ t, kineticEnergy L V t ≤ B := by
  obtain ⟨B, hB, hb⟩ := hb []
  exact ⟨(1 / 2 : ℝ) * volume.real (fundamentalCube L) * (3 * B^2),
    fun t => kineticEnergy_bound hV L hB hb t⟩

end ShearFlows

end

end OAI
