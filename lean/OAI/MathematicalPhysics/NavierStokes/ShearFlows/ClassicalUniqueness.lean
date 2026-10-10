import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EnergyComparison
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ForceIdentities
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.MaterialFlow

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

theorem dot_continuousOn {E : Type*} [TopologicalSpace E] {s : Set E} {f g : E → Space}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => dot (f x) (g x)) s := by
  apply continuousOn_finsetSum
  intro j _
  exact ((continuous_apply j).comp_continuousOn hf).mul
    ((continuous_apply j).comp_continuousOn hg)

theorem zero_of_energy_inequality {E : ℝ → ℝ} {T C : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn E (Icc 0 T)) (h0 : E 0 = 0) (hpos : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (hd : ∀ t ∈ Ioo 0 T, ∃ e, HasDerivAt E e t ∧ e ≤ C * E t) : E T = 0 := by
  let H : ℝ → ℝ := fun t => Real.exp (-C * t) * E t
  have hHc : ContinuousOn H (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hc
  have hHd (t : ℝ) (ht : t ∈ Ioo 0 T) : ∃ e, HasDerivAt H e t ∧ e ≤ 0 := by
    obtain ⟨e,he,heC⟩ := hd t ht
    have hexp := ((hasDerivAt_id t).const_mul (-C)).exp
    refine ⟨_,hexp.fun_mul he,?_⟩
    dsimp
    have hm := mul_le_mul_of_nonneg_left heC (Real.exp_pos (-C*t)).le
    nlinarith
  have hant : AntitoneOn H (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hHc
    · intro t ht
      obtain ⟨e,he,_⟩ := hHd t (by simpa only [interior_Icc] using ht)
      exact he.differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨e,he,he0⟩ := hHd t (by simpa only [interior_Icc] using ht)
      simpa only [he.deriv] using he0
  have hle := hant ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT
  have hz : Real.exp (-C*T) * E T ≤ 0 := by simpa [H,h0] using hle
  have hne := hpos T ⟨hT,le_rfl⟩
  have hp := Real.exp_pos (-C*T)
  nlinarith

theorem fundamentalCube_closure_interior {L : ℝ} (hL : 0 < L) :
    closure (interior (fundamentalCube L)) = fundamentalCube L := by
  unfold fundamentalCube
  rw [← pi_univ_Icc, interior_pi_set (finite_univ), closure_pi_set]
  simp only [Pi.zero_apply, interior_Icc, closure_Ioo hL.ne, pi_univ_Icc]

theorem periodic_field_zero_of_energy_zero {L : ℝ} (hL : 0 < L) {W : Space → Space}
    (hW : Continuous W) (hp : CubePeriodic L W)
    (hE : (∫ x in fundamentalCube L, dot (W x) (W x)) = 0) : ∀ x, W x = 0 := by
  have hi : IntegrableOn (fun x => dot (W x) (W x)) (fundamentalCube L) :=
    (dot_continuous hW hW).integrableOn_Icc
  have hae : (fun x => dot (W x) (W x)) =ᵐ[volume.restrict (fundamentalCube L)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall (fun x => dot_self_nonneg _)) hi).mp hE
  have he := Measure.eqOn_of_ae_eq hae (dot_continuous hW hW).continuousOn
    continuousOn_const (by rw [fundamentalCube_closure_interior hL])
  intro x
  obtain ⟨y,hy,n,hx⟩ := fundamentalCube_representative hL x
  rw [hx,hp]
  have hn := norm_sq_le_dot_self (W y)
  have hz : dot (W y) (W y) = 0 := he hy
  have hnorm : ‖W y‖ = 0 := by nlinarith [norm_nonneg (W y)]
  exact norm_eq_zero.mp hnorm

theorem classical_velocity_unique {L ν B : ℝ} (hL : 0 < L) (hν : 0 ≤ ν)
    {f u v : Velocity} {p : Pressure}
    (hu : IsClassicalSolution L ν f u p) (hv : IsClassicalSolution L ν f v (fun _ => 0))
    (hB : ∀ t, 0 ≤ t → ∀ x, ‖fderiv ℝ (fun y => v (t,y)) x‖ ≤ B) :
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
  have hineq (t : ℝ) (ht : 0 ≤ t) :
      (∫ x in fundamentalCube L, dot (W (t,x)) (G (t,x))) ≤ 3 * B * E t := by
    apply integrated_comparison_inequality hL.le hν (hWs t ht)
      ((hu.regularity.spatial_u t ht).of_le (by norm_num))
      ((hv.regularity.spatial_u t ht).of_le (by norm_num))
      (hu.regularity.spatial_p t ht) (hWp t ht) (hu.periodic_u t ht) (hu.periodic_p t ht)
    · intro x
      rw [divergence_sub ((hu.regularity.spatial_u t ht).differentiable (by norm_num))
          ((hv.regularity.spatial_u t ht).differentiable (by norm_num)),
        hu.divergence_zero t ht, hv.divergence_zero t ht, sub_self]
    · exact hu.divergence_zero t ht
    · exact hB t ht
    · intro x
      dsimp only [G, W]
      rw [← initialTimeDerivative_sub (hu.regularity.temporal_u t ht x)
        (hv.regularity.temporal_u t ht x)]
      exact classical_difference_equation hu hv ht x
  intro t ht x
  have hEt : E t = 0 := by
    apply zero_of_energy_inequality (C := 6*B) ht (hEc t ht) hE0 (fun s _ => hEpos s)
    intro s hs
    refine ⟨_,hEd t ht s hs,?_⟩
    have hh := hineq s hs.1.le
    nlinarith
  exact sub_eq_zero.mp (periodic_field_zero_of_energy_zero hL (hWs t ht).continuous (hWp t ht) hEt x)

theorem classical_pressure_unique {L ν : ℝ} (hL : 0 < L) {f u v : Velocity} {p : Pressure}
    (hu : IsClassicalSolution L ν f u p) (hv : IsClassicalSolution L ν f v (fun _ => 0))
    (heq : ∀ t, 0 ≤ t → ∀ x, u (t,x) = v (t,x)) :
    ∀ t, 0 ≤ t → ∀ x, p (t,x) = 0 := by
  intro t ht
  have htime (x : Space) : initialTimeDerivative u t x = initialTimeDerivative v t x :=
    derivWithin_congr (fun s hs => heq s hs x) (heq t ht x)
  have hspace : (fun x => u (t,x)) = fun x => v (t,x) := funext (heq t ht)
  have hgrad (x : Space) : gradient (fun y => p (t,y)) x = 0 := by
    have h1 := hu.equation t ht x
    have h2 := hv.equation t ht x
    rw [htime, hspace] at h1
    have hz : gradient (fun _ : Space => (0 : ℝ)) x = 0 := by ext j; simp [gradient]
    rw [hz, neg_zero, zero_add] at h2
    linear_combination h1 - h2
  have hder (x : Space) : fderiv ℝ (fun y => p (t,y)) x = 0 := by
    ext w
    rw [← coordinate_trace]
    have hz (j : Fin 3) : fderiv ℝ (fun y => p (t,y)) x (basis j) = 0 := congrFun (hgrad x) j
    simp [hz]
  have hconst (x : Space) : p (t,x) = p (t,0) :=
    is_const_of_fderiv_eq_zero ((hu.regularity.spatial_p t ht).differentiable (by norm_num)) hder x 0
  have hc0 := hu.pressure_mean t ht
  simp_rw [hconst] at hc0
  have hvol : (volume (fundamentalCube L)).toReal = L^3 := by
    rw [fundamentalCube, Real.volume_Icc_pi_toReal (a := (0 : Space)) (b := fun _ => L) (fun _ => hL.le)]
    simp
  simp only [setIntegral_const, smul_eq_mul, Measure.real, hvol] at hc0
  intro x
  rw [hconst]
  exact (mul_eq_zero.mp hc0).resolve_left (pow_ne_zero 3 hL.ne')

theorem smooth_periodic_classical_unique {L ν : ℝ} (hL : 0 < L) (hν : 0 < ν)
    {f V : Velocity} (hV : ContDiff ℝ ∞ V) (hp : SpatiallyPeriodic L V) (ht : TimePeriodic V)
    (hsol : IsClassicalSolution L ν f V (fun _ => 0)) :
    ∀ u p, IsClassicalSolution L ν f u p →
    ∀ t, 0 ≤ t → ∀ x, u (t,x) = V (t,x) ∧ p (t,x) = 0 := by
  obtain ⟨K,hK⟩ := smooth_periodic_lipschitz hL hV hp ht
  have hsp (t : ℝ) : LipschitzWith K (fun x => V (t,x)) := by
    intro x y
    simpa [Prod.edist_eq] using hK.edist_le_mul (t,x) (t,y)
  have hbound (t : ℝ) (_ : 0 ≤ t) (x : Space) :
      ‖fderiv ℝ (fun y => V (t,y)) x‖ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz ℝ (hsp t)
  intro u p hu
  have heq := classical_velocity_unique hL hν.le hu hsol hbound
  have heqp := classical_pressure_unique hL hu hsol heq
  exact fun t ht x => ⟨heq t ht x,heqp t ht x⟩

theorem realizingVelocity_unique {d : Input} (hd : ValidInput d) {ν : ℝ} (hν : 0 < ν) :
    ∀ u p, IsClassicalSolution d.period ν (force ν d.realizingVelocity) u p →
    ∀ t, 0 ≤ t → ∀ x, u (t,x) = d.realizingVelocity (t,x) ∧ p (t,x) = 0 :=
  smooth_periodic_classical_unique (by exact_mod_cast hd.period_pos) hν
    (realizingVelocity_smooth hd) (realizingVelocity_spatially_periodic d)
    (realizingVelocity_time_periodic d) (realizingVelocity_solves_NS hd ν)

end ShearFlows

end

end OAI
