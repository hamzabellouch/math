import Mathlib
import OAI.Geometry.NearbyLagrangian.HomogeneousFunctions

namespace OAI

/-! Gradient bounds and regular radial parametrization of critical loci. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes.RegularHomogeneous

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem gradient_bounds [ProperSpace W] [Nontrivial W] (f : RegularHomogeneous W) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ w : W, c * ‖w‖ ≤ ‖gradient f w‖ ∧ ‖gradient f w‖ ≤ C * ‖w‖ := by
  have hne : (Metric.sphere (0 : W) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  have hc : ContinuousOn (fun w : W => ‖gradient f w‖) (Metric.sphere (0 : W) 1) :=
    f.continuous_gradient.norm.continuousOn
  obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_sphere (0 : W) 1).exists_isMinOn hne hc
  obtain ⟨u₁, hu₁, hmax⟩ := (isCompact_sphere (0 : W) 1).exists_isMaxOn hne hc
  have hnorm₀ : ‖u₀‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu₀
  have hnorm₁ : ‖u₁‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu₁
  have hpos₀ : 0 < ‖gradient f u₀‖ := norm_pos_iff.mpr
    (f.gradient_ne_zero (norm_ne_zero_iff.mp (by rw [hnorm₀]; norm_num)))
  have hpos₁ : 0 < ‖gradient f u₁‖ := norm_pos_iff.mpr
    (f.gradient_ne_zero (norm_ne_zero_iff.mp (by rw [hnorm₁]; norm_num)))
  refine ⟨‖gradient f u₀‖, ‖gradient f u₁‖, hpos₀, hpos₁, ?_⟩
  intro w
  by_cases hw : w = 0
  · simp [hw]
  have hn := norm_pos_iff.mpr hw
  let u := ‖w‖⁻¹ • w
  have hu : u ∈ Metric.sphere (0 : W) 1 := by
    simp only [u, Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
  have hre : ‖w‖ • u = w := by simp [u, smul_smul, hn.ne']
  have hrad : ‖gradient f w‖ = ‖w‖ * ‖gradient f u‖ := by
    calc
      ‖gradient f w‖ = ‖gradient f (‖w‖ • u)‖ := by rw [hre]
      _ = ‖w‖ * ‖gradient f u‖ := by
        rw [f.gradient_smul hn, norm_smul, Real.norm_eq_abs, abs_norm]
  rw [hrad, mul_comm ‖w‖]
  exact ⟨mul_le_mul_of_nonneg_right (hmin hu) hn.le,
    mul_le_mul_of_nonneg_right (hmax hu) hn.le⟩

omit [InnerProductSpace ℝ W] [CompleteSpace W] in
private theorem unit_ne_zero (u : Metric.sphere (0 : W) 1) : (u : W) ≠ 0 := by
  have hu : ‖(u : W)‖ = 1 := by simp
  exact norm_ne_zero_iff.mp (by rw [hu]; norm_num)

def angularPosition (w : W) (hw : w ≠ 0) : Metric.sphere (0 : W) 1 :=
  ⟨‖w‖⁻¹ • w, by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)⟩

omit [CompleteSpace W] in
@[simp] theorem norm_smul_angularPosition (w : W) (hw : w ≠ 0) :
    ‖w‖ • (angularPosition w hw : W) = w := by
  simp only [angularPosition, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw),
    one_smul]

@[simp] theorem angularPosition_radialSolution (f : RegularHomogeneous W) (R : ℝ)
    (hR : 0 < R) (u : Metric.sphere (0 : W) 1) :
    angularPosition (f.radialSolution R u) (f.radialSolution_ne_zero R hR u) = u := by
  apply Subtype.ext
  change ‖f.radialSolution R u‖⁻¹ • f.radialSolution R u = (u : W)
  rw [f.radialSolution_norm R hR, radialSolution, smul_smul,
    inv_mul_cancel₀ (div_ne_zero hR.ne'
      (norm_ne_zero_iff.mpr (f.gradient_ne_zero (unit_ne_zero u)))), one_smul]

theorem continuous_direction (f : RegularHomogeneous W) : Continuous f.direction := by
  apply Continuous.subtype_mk
  exact ((f.continuous_gradient.comp continuous_subtype_val).norm.inv₀
    (fun u => norm_ne_zero_iff.mpr (f.gradient_ne_zero (unit_ne_zero u)))).smul
    (f.continuous_gradient.comp continuous_subtype_val)

theorem continuous_radialSolution (f : RegularHomogeneous W) (R : ℝ) :
    Continuous (f.radialSolution R) := by
  exact (continuous_const.div (f.continuous_gradient.comp continuous_subtype_val).norm
    (fun u => norm_ne_zero_iff.mpr (f.gradient_ne_zero (unit_ne_zero u)))).smul
    continuous_subtype_val

def CriticalLocus (f : RegularHomogeneous W) (R : ℝ) :=
  { p : W × Metric.sphere (0 : W) 1 // gradient f p.1 = R • (p.2 : W) }

instance (f : RegularHomogeneous W) (R : ℝ) : TopologicalSpace (f.CriticalLocus R) :=
  inferInstanceAs (TopologicalSpace
    { p : W × Metric.sphere (0 : W) 1 // gradient f p.1 = R • (p.2 : W) })

theorem critical_ne_zero (f : RegularHomogeneous W) (R : ℝ) (hR : 0 < R)
    (p : f.CriticalLocus R) : p.val.1 ≠ 0 := by
  intro h
  have he := p.property
  rw [h, f.gradient_zero] at he
  exact smul_ne_zero hR.ne' (unit_ne_zero p.val.2) he.symm

theorem critical_gradient_norm (f : RegularHomogeneous W) (R : ℝ) (hR : 0 < R)
    (p : f.CriticalLocus R) : ‖gradient f p.val.1‖ = R := by
  rw [p.property, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  simp

private theorem critical_radial_recovery (f : RegularHomogeneous W) (R : ℝ)
    (hR : 0 < R) (p : f.CriticalLocus R) :
    f.radialSolution R (angularPosition p.val.1 (f.critical_ne_zero R hR p)) = p.val.1 := by
  let u := angularPosition p.val.1 (f.critical_ne_zero R hR p)
  have hw : 0 < ‖p.val.1‖ := norm_pos_iff.mpr (f.critical_ne_zero R hR p)
  have hn : 0 < ‖gradient f u‖ := norm_pos_iff.mpr (f.gradient_ne_zero (unit_ne_zero u))
  have he : R = ‖p.val.1‖ * ‖gradient f u‖ := by
    calc
      R = ‖gradient f p.val.1‖ := (f.critical_gradient_norm R hR p).symm
      _ = ‖gradient f (‖p.val.1‖ • (u : W))‖ := by
        rw [norm_smul_angularPosition]
      _ = ‖p.val.1‖ * ‖gradient f u‖ := by
        rw [f.gradient_smul hw, norm_smul, Real.norm_eq_abs, abs_norm]
  change (R / ‖gradient f u‖) • (u : W) = p.val.1
  have hr : R / ‖gradient f u‖ = ‖p.val.1‖ := (div_eq_iff hn.ne').mpr he
  rw [hr, norm_smul_angularPosition]

def criticalHomeomorph (f : RegularHomogeneous W) (R : ℝ) (hR : 0 < R) :
    Metric.sphere (0 : W) 1 ≃ₜ f.CriticalLocus R where
  toFun u := ⟨(f.radialSolution R u, f.direction u), f.radialSolution_critical R hR u⟩
  invFun p := angularPosition p.val.1 (f.critical_ne_zero R hR p)
  left_inv u := f.angularPosition_radialSolution R hR u
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact f.critical_radial_recovery R hR p
    · apply Subtype.ext
      apply (smul_right_injective W hR.ne')
      change R • (f.direction (angularPosition p.val.1 (f.critical_ne_zero R hR p)) : W) =
        R • (p.val.2 : W)
      exact (f.radialSolution_critical R hR _).symm.trans
        ((congrArg (gradient f) (f.critical_radial_recovery R hR p)).trans p.property)
  continuous_toFun := ((f.continuous_radialSolution R).prodMk f.continuous_direction).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((continuous_fst.comp continuous_subtype_val).norm.inv₀
      (fun p => norm_ne_zero_iff.mpr (f.critical_ne_zero R hR p))).smul
      (continuous_fst.comp continuous_subtype_val)

theorem continuous_family_gradient [ProperSpace W] {B : Type*} [TopologicalSpace B]
    {f : B → RegularHomogeneous W} (hf : Continuous f) :
    Continuous (fun p : B × Metric.sphere (0 : W) 1 => gradient (f p.1) p.2) := by
  have hj : Continuous (jet (W := W)) := continuous_induced_dom
  have hd : Continuous (fun p : B × Metric.sphere (0 : W) 1 =>
      fderiv ℝ (f p.1) p.2) :=
    continuous_eval.comp ((((hj.comp hf).snd).comp continuous_fst).prodMk continuous_snd)
  exact (InnerProductSpace.toDual ℝ W).symm.continuous.comp hd

theorem uniform_gradient_bounds [ProperSpace W] [Nontrivial W]
    {B : Type*} [TopologicalSpace B] [CompactSpace B] [Nonempty B]
    {f : B → RegularHomogeneous W} (hf : Continuous f) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ b : B, ∀ w : W, c * ‖w‖ ≤ ‖gradient (f b) w‖ ∧
        ‖gradient (f b) w‖ ≤ C * ‖w‖ := by
  have : Nonempty (Metric.sphere (0 : W) 1) :=
    (NormedSpace.sphere_nonempty.mpr (by norm_num)).to_subtype
  have hc := (continuous_family_gradient hf).norm
  obtain ⟨p₀, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (univ : Set (B × Metric.sphere (0 : W) 1)).Nonempty) hc.continuousOn
  obtain ⟨p₁, _, hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (univ : Set (B × Metric.sphere (0 : W) 1)).Nonempty) hc.continuousOn
  have hpos₀ : 0 < ‖gradient (f p₀.1) p₀.2‖ :=
    norm_pos_iff.mpr ((f p₀.1).gradient_ne_zero (unit_ne_zero p₀.2))
  have hpos₁ : 0 < ‖gradient (f p₁.1) p₁.2‖ :=
    norm_pos_iff.mpr ((f p₁.1).gradient_ne_zero (unit_ne_zero p₁.2))
  refine ⟨‖gradient (f p₀.1) p₀.2‖, ‖gradient (f p₁.1) p₁.2‖, hpos₀, hpos₁, ?_⟩
  intro b w
  by_cases hw : w = 0
  · simp [hw]
  let u := angularPosition w hw
  have hn := norm_pos_iff.mpr hw
  have he : ‖gradient (f b) w‖ = ‖w‖ * ‖gradient (f b) u‖ := by
    calc
      ‖gradient (f b) w‖ = ‖gradient (f b) (‖w‖ • (u : W))‖ := by
        rw [norm_smul_angularPosition]
      _ = ‖w‖ * ‖gradient (f b) u‖ := by
        rw [(f b).gradient_smul hn, norm_smul, Real.norm_eq_abs, abs_norm]
  rw [he, mul_comm ‖w‖]
  exact ⟨mul_le_mul_of_nonneg_right (hmin (mem_univ (b, u))) hn.le,
    mul_le_mul_of_nonneg_right (hmax (mem_univ (b, u))) hn.le⟩

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous

open scoped Manifold

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem exists_tangent_derivative (f : RegularHomogeneous W)
    (u : Metric.sphere (0 : W) 1) (hu : f u = 0) :
    ∃ v : W, ⟪(u : W), v⟫_ℝ = 0 ∧ fderiv ℝ f u v ≠ 0 := by
  have hne := f.regular (u : W) (unit_ne_zero u)
  have hv : ∃ v : W, fderiv ℝ f u v ≠ 0 := by
    by_contra! hall
    apply hne
    ext v
    exact hall v
  obtain ⟨v, hv⟩ := hv
  refine ⟨v - ⟪(u : W), v⟫_ℝ • (u : W), ?_, ?_⟩
  · rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    simp
  · simpa only [map_sub, map_smul, f.euler, hu, mul_zero, smul_zero, sub_zero] using hv

theorem angular_zero_regular [FiniteDimensional ℝ W] {n : ℕ}
    [Fact (Module.finrank ℝ W = n + 1)] (f : RegularHomogeneous W)
    (u : Metric.sphere (0 : W) 1) (hu : f u = 0) :
    Function.Surjective (mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun v : Metric.sphere (0 : W) 1 => f v) u) := by
  obtain ⟨v, hvperp, hvne⟩ := f.exists_tangent_derivative u hu
  have hvrange : v ∈ (mvfderiv (𝓡 n)
      ((↑) : Metric.sphere (0 : W) 1 → W) u).range := by
    rw [range_mvfderiv_subtypeVal]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hvperp
  obtain ⟨a, ha⟩ := hvrange
  change (mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) u) a = v at ha
  have hcomp : mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun v : Metric.sphere (0 : W) 1 => f v) u =
      (fderiv ℝ f (u : W)).comp
        (mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) u) := by
    have hc := mfderiv_comp u
      (mdifferentiableAt_iff_differentiableAt.mpr (f.differentiable (u : W)))
      ((contMDiff_coe_sphere (n := n) (m := (1 : ℕ∞ω)) u).mdifferentiableAt one_ne_zero)
    convert! hc using 2
    simp only [mfderiv_eq_fderiv]
    rfl
  intro t
  change ℝ at t
  refine ⟨(t / fderiv ℝ f u v) • a, ?_⟩
  rw [hcomp]
  change ((fderiv ℝ f (u : W)).comp
    (mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) u))
      ((t / fderiv ℝ f u v) • a) = t
  rw [map_smul]
  simp only [ContinuousLinearMap.comp_apply, ha, smul_eq_mul]
  exact div_mul_cancel₀ t hvne

end NearbyLagrangian.Tubes.RegularHomogeneous

end

end OAI
