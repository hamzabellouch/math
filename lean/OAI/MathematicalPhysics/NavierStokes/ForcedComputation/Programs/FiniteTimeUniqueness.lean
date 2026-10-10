import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ClassicalUniqueness

namespace OAI

/-! The energy uniqueness argument only needs a derivative bound on each
finite interval. This covers the increasing-speed torus detector. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped ContDiff

theorem finite_interval_classical_velocity_unique {L ν : ℝ} (hL : 0 < L) (hν : 0 ≤ ν)
    {f u v : Velocity} {p : Pressure}
    (hu : IsClassicalSolution L ν f u p) (hv : IsClassicalSolution L ν f v (fun _ => 0))
    (hb : ∀ T, 0 ≤ T → ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ x,
      ‖fderiv ℝ (fun y => v (t,y)) x‖ ≤ B) :
    ∀ t, 0 ≤ t → ∀ x, u (t,x) = v (t,x) := by
  let W : Velocity := fun y => u y - v y
  let G : Velocity := fun y => initialTimeDerivative u y.1 y.2 - initialTimeDerivative v y.1 y.2
  let E : ℝ → ℝ := fun t => ∫ x in fundamentalCube L, dot (W (t,x)) (W (t,x))
  have hWs (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ 2 (fun x => W (t,x)) :=
    (hu.regularity.spatial_u t ht).sub (hv.regularity.spatial_u t ht)
  have hWp (t : ℝ) (ht : 0 ≤ t) : CubePeriodic L (fun x => W (t,x)) := by
    intro x n
    dsimp [W]
    rw [hu.periodic_u t ht, hv.periodic_u t ht]
  have hWc (T : ℝ) (hT : 0 ≤ T) : ContinuousOn W (timeCylinder T) :=
    (hu.regularity.continuous_u T hT).sub (hv.regularity.continuous_u T hT)
  have hGc (T : ℝ) (hT : 0 ≤ T) : ContinuousOn G (timeCylinder T) :=
    (hu.regularity.continuous_ut T hT).sub (hv.regularity.continuous_ut T hT)
  have hGd (t : ℝ) (ht : 0 < t) (x : Space) : HasDerivAt (fun s => W (s,x)) (G (t,x)) t :=
    ((hu.regularity.temporal_u t ht.le x).hasDerivWithinAt.hasDerivAt (Ici_mem_nhds ht)).sub
      ((hv.regularity.temporal_u t ht.le x).hasDerivWithinAt.hasDerivAt (Ici_mem_nhds ht))
  have hE0 : E 0 = 0 := by simp [E,W,hu.initial,hv.initial]
  have hEpos (t : ℝ) : 0 ≤ E t := integral_nonneg (fun _ => dot_self_nonneg _)
  have hEc (T : ℝ) (hT : 0 ≤ T) : ContinuousOn E (Icc 0 T) :=
    continuousOn_cube_integral (dot_continuousOn (hWc T hT) (hWc T hT))
  have hEd (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt E (2 * ∫ x in fundamentalCube L, dot (W (t,x)) (G (t,x))) t := by
    have hh := hasDerivAt_cube_integral (L := L)
      (dot_continuousOn (hWc T hT) (hWc T hT))
      (continuousOn_const.mul (dot_continuousOn (hWc T hT) (hGc T hT)))
      (fun s hs x => hasDerivAt_dot_self (hGd s hs.1 x)) ht
    simpa only [Pi.mul_apply, integral_const_mul] using hh
  intro T hT x
  obtain ⟨B, hB⟩ := hb T hT
  have hineq (t : ℝ) (htT : t ∈ Icc 0 T) :
      (∫ x in fundamentalCube L, dot (W (t,x)) (G (t,x))) ≤ 3 * B * E t := by
    have ht : 0 ≤ t := htT.1

    apply integrated_comparison_inequality hL.le hν (hWs t ht)
      ((hu.regularity.spatial_u t ht).of_le (by norm_num))
      ((hv.regularity.spatial_u t ht).of_le (by norm_num))
      (hu.regularity.spatial_p t ht) (hWp t ht) (hu.periodic_u t ht) (hu.periodic_p t ht)
    · intro x
      rw [divergence_sub ((hu.regularity.spatial_u t ht).differentiable (by norm_num))
          ((hv.regularity.spatial_u t ht).differentiable (by norm_num)),
        hu.divergence_zero t ht, hv.divergence_zero t ht, sub_self]
    · exact hu.divergence_zero t ht
    · exact hB t htT
    · intro x
      dsimp only [G, W]
      rw [← initialTimeDerivative_sub (hu.regularity.temporal_u t ht x)
        (hv.regularity.temporal_u t ht x)]
      exact classical_difference_equation hu hv ht x
  have hEt : E T = 0 := by
    apply zero_of_energy_inequality (C := 6 * B) hT (hEc T hT) hE0 (fun s _ => hEpos s)
    intro s hs
    refine ⟨_, hEd T hT s hs, ?_⟩
    have hh := hineq s ⟨hs.1.le, hs.2.le⟩
    nlinarith
  exact sub_eq_zero.mp (periodic_field_zero_of_energy_zero hL (hWs T hT).continuous
    (hWp T hT) hEt x)

private theorem compact_scalar_bound {L T : ℝ} {g : SpaceTime → ℝ}
    (hg : ContinuousOn g (Icc 0 T ×ˢ fundamentalCube L)) :
    ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ x ∈ fundamentalCube L, g (t, x) ≤ B := by
  have hk : IsCompact (Icc (0 : ℝ) T ×ˢ fundamentalCube L) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hk.bddAbove_image hg
  refine ⟨B, ?_⟩
  intro t ht x hx
  exact hB ⟨(t, x), ⟨ht, hx⟩, rfl⟩

theorem classical_compact_derivative_bound {L ν : ℝ}
    {f v : Velocity} {p : Pressure} (hv : IsClassicalSolution L ν f v p)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ x ∈ fundamentalCube L,
      ‖fderiv ℝ (fun y => v (t,y)) x‖ ≤ B := by
  let D : SpaceTime → Space →L[ℝ] Space := fun y => fderiv ℝ (fun x => v (y.1, x)) y.2
  have hc : ContinuousOn D (Icc 0 T ×ˢ fundamentalCube L) :=
    (hv.regularity.continuous_du T hT).mono (fun _ hy => ⟨hy.1, mem_univ _⟩)
  exact compact_scalar_bound (g := fun y => ‖D y‖) hc.norm

theorem classical_spatial_derivative_periodic {L ν : ℝ}
    {f v : Velocity} {p : Pressure} (hv : IsClassicalSolution L ν f v p)
    {t : ℝ} (ht : 0 ≤ t) : CubePeriodic L (fderiv ℝ (fun x => v (t, x))) := by
  have hd : Differentiable ℝ (fun x => v (t, x)) :=
    (hv.regularity.spatial_u t ht).differentiable (by norm_num)
  exact CubePeriodic.fderiv (hv.periodic_u t ht) hd

theorem classical_finite_derivative_bound {L ν : ℝ} (hL : 0 < L)
    {f v : Velocity} {p : Pressure} (hv : IsClassicalSolution L ν f v p)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (fun y => v (t,y)) x‖ ≤ B := by
  obtain ⟨B, hB⟩ := classical_compact_derivative_bound hv T hT
  refine ⟨B, ?_⟩
  intro t ht x
  obtain ⟨y, hy, n, rfl⟩ := fundamentalCube_representative hL x
  rw [classical_spatial_derivative_periodic hv ht.1 y n]
  exact hB t ht y hy

theorem finite_time_classical_unique {L ν : ℝ} (hL : 0 < L) (hν : 0 ≤ ν)
    {f v : Velocity} (hv : IsClassicalSolution L ν f v (fun _ => 0)) :
    ∀ u p, IsClassicalSolution L ν f u p →
      ∀ t, 0 ≤ t → ∀ x, u (t,x) = v (t,x) ∧ p (t,x) = 0 := by
  intro u p hu
  have he := finite_interval_classical_velocity_unique hL hν hu hv
    (classical_finite_derivative_bound hL hv)
  have hp := classical_pressure_unique hL hu hv he
  exact fun t ht x => ⟨he t ht x, hp t ht x⟩

end ForcedComputation.VelocityDetector

end

end OAI
