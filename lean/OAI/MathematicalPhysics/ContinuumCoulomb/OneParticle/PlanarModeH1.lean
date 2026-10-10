import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarSobolev

namespace OAI

/-! Membership of the manufactured mode in the closed planar Sobolev
graph, obtained by expanding compact cutoffs. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace ContinuumCoulomb
namespace PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance : BorelSpace PlanarPosition := ⟨rfl⟩
local instance : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

def cutoffBump : ContDiffBump (0 : PlanarPosition) := ⟨1, 2, by norm_num, by norm_num⟩

theorem cutoffBump_smooth : ContDiff ℝ ∞ (cutoffBump : PlanarPosition → ℝ) := cutoffBump.contDiff

def cutoffScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

def cutoff (n : ℕ) (x : PlanarPosition) : ℝ := cutoffBump (cutoffScale n • x)

theorem cutoffScale_positive (n : ℕ) : 0 < cutoffScale n := inv_pos.mpr (by positivity)

theorem cutoffScale_le_one (n : ℕ) : cutoffScale n ≤ 1 := by
  unfold cutoffScale
  apply inv_le_one_of_one_le₀
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem cutoffScale_tendsto : Tendsto cutoffScale atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  cutoffBump_smooth.comp (contDiff_const_smul (cutoffScale n))

theorem cutoff_nonnegative (n : ℕ) (x : PlanarPosition) : 0 ≤ cutoff n x := cutoffBump.nonneg

theorem cutoff_le_one (n : ℕ) (x : PlanarPosition) : cutoff n x ≤ 1 := cutoffBump.le_one

theorem cutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (cutoff n) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : PlanarPosition) (2 * (n + 1 : ℝ)))
  intro x hx
  have hdist : 2 * (n + 1 : ℝ) < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  apply cutoffBump.zero_of_le_dist
  change 2 ≤ dist (cutoffScale n • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_positive n)]
  change 2 ≤ (n + 1 : ℝ)⁻¹ * ‖x‖
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ (by positivity)).mpr hdist.le

theorem cutoff_tendsto (x : PlanarPosition) :
    Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have h := (cutoffBump_smooth.continuous.tendsto 0).comp
    (by simpa only [zero_smul] using cutoffScale_tendsto.smul_const x)
  have hzero : cutoffBump (0 : PlanarPosition) = 1 :=
    cutoffBump.one_of_mem_closedBall (by simp [cutoffBump])
  simpa only [Function.comp_def, cutoff, hzero] using h

theorem cutoff_fderiv (n : ℕ) (x : PlanarPosition) :
    fderiv ℝ (cutoff n) x = cutoffScale n • fderiv ℝ cutoffBump (cutoffScale n • x) := by
  have h := (cutoffBump_smooth.differentiable (by simp) (cutoffScale n • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (cutoffScale n))
  change fderiv ℝ (cutoffBump ∘ fun y => cutoffScale n • y) x = _
  rw [h.fderiv]
  ext e
  simp

theorem cutoff_grad (n : ℕ) (x : PlanarPosition) :
    grad (cutoff n) x = cutoffScale n • grad cutoffBump (cutoffScale n • x) := by
  simp only [grad, cutoff_fderiv, map_smul]

theorem cutoff_grad_tendsto (x : PlanarPosition) :
    Tendsto (fun n => grad (cutoff n) x) atTop (𝓝 0) := by
  simp_rw [cutoff_grad]
  have h := ((continuous_grad (cutoffBump_smooth.of_le (by simp))).tendsto 0).comp
    (by simpa only [zero_smul] using cutoffScale_tendsto.smul_const x)
  simpa only [zero_smul, Function.comp_def] using cutoffScale_tendsto.smul h

private theorem bump_grad_bounded : ∃ C : ℝ, ∀ x, ‖grad cutoffBump x‖ ≤ C :=
  (continuous_grad (cutoffBump_smooth.of_le (by simp))).bounded_above_of_compact_support
    (hasCompactSupport_grad cutoffBump.hasCompactSupport)

def cutoffGradBound : ℝ := Classical.choose bump_grad_bounded

theorem cutoffGradBound_spec (x : PlanarPosition) : ‖grad cutoffBump x‖ ≤ cutoffGradBound :=
  Classical.choose_spec bump_grad_bounded x

theorem cutoffGradBound_nonnegative : 0 ≤ cutoffGradBound :=
  (norm_nonneg (grad cutoffBump 0)).trans (Classical.choose_spec bump_grad_bounded 0)

theorem cutoff_grad_bound (n : ℕ) (x : PlanarPosition) :
    ‖grad (cutoff n) x‖ ≤ cutoffGradBound := by
  rw [cutoff_grad, norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_positive n)]
  exact (mul_le_mul_of_nonneg_left (Classical.choose_spec bump_grad_bounded _)
    (cutoffScale_positive n).le).trans
    (mul_le_of_le_one_left cutoffGradBound_nonnegative (cutoffScale_le_one n))

theorem mode_square_integrable : Integrable (fun x => planarResolventMode x ^ 2) :=
  (planar_integrable_change_borel (borel PlanarPosition) ⟨rfl⟩ _).mpr
    planarResolventMode_square_integrable

theorem mode_memLp : MemLp planarResolventMode 2 :=
  (memLp_two_iff_integrable_sq planarResolventMode_C7.continuous.aestronglyMeasurable).mpr
    mode_square_integrable

theorem grad_norm_sq (f : PlanarPosition → ℝ) (x : PlanarPosition) :
    ‖grad f x‖ ^ 2 = ∑ a : Fin 2, planarPartial f (planarAxis a) x ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_congr rfl (fun a _ => congrArg (fun t : ℝ => t ^ 2) (grad_coordinate f x a))

theorem mode_grad_square_integrable : Integrable (fun x => ‖grad planarResolventMode x‖ ^ 2) := by
  have hi (a : Fin 2) : Integrable (fun x => planarPartial planarResolventMode (planarAxis a) x ^ 2) :=
    (planar_integrable_change_borel (borel PlanarPosition) ⟨rfl⟩ _).mpr
      (planarResolventMode_partial_square_integrable (planarAxis a))
  have h := integrable_finsetSum Finset.univ (fun a _ => hi a)
  exact h.congr (Filter.Eventually.of_forall (fun x => (grad_norm_sq planarResolventMode x).symm))

theorem mode_grad_memLp : MemLp (grad planarResolventMode) 2 :=
  (memLp_two_iff_integrable_sq_norm
    (continuous_grad (planarResolventMode_C7.of_le (by norm_num))).aestronglyMeasurable).mpr
      mode_grad_square_integrable

def cutoffMode (n : ℕ) : Test := ⟨fun x => cutoff n x * planarResolventMode x,
  ⟨((cutoff_smooth n).of_le (by simp)).mul (planarResolventMode_C7.of_le (by norm_num)),
    (cutoff_hasCompactSupport n).mul_right⟩⟩

theorem cutoffMode_grad (n : ℕ) (x : PlanarPosition) :
    grad (cutoffMode n).val x = cutoff n x • grad planarResolventMode x +
      planarResolventMode x • grad (cutoff n) x := by
  ext a
  rw [grad_coordinate]
  change planarPartial (fun y => cutoff n y * planarResolventMode y) (planarAxis a) x = _
  rw [planarPartial_mul _ _ ((cutoff_smooth n).of_le (by simp))
    (planarResolventMode_C7.of_le (by norm_num))]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, grad_coordinate]

theorem cutoffMode_grad_tendsto (x : PlanarPosition) :
    Tendsto (fun n => grad (cutoffMode n).val x) atTop (𝓝 (grad planarResolventMode x)) := by
  simp_rw [cutoffMode_grad]
  simpa only [one_smul, smul_zero, add_zero] using
    ((cutoff_tendsto x).smul_const (grad planarResolventMode x)).add
      ((tendsto_const_nhds (x := planarResolventMode x)).smul (cutoff_grad_tendsto x))

private theorem toLp_sub_norm_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f g : PlanarPosition → F}
    (hf : MemLp f 2 (volume : Measure PlanarPosition))
    (hg : MemLp g 2 (volume : Measure PlanarPosition)) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with x hx hxf hxg
  simp only [real_inner_self_eq_norm_sq, hx, Pi.sub_apply, hxf, hxg]

private theorem toLp_tendsto_of_integral_sub_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f : ℕ → PlanarPosition → F} {g : PlanarPosition → F}
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure PlanarPosition))
    (hg : MemLp g 2 (volume : Measure PlanarPosition))
    (hlim : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hs : Tendsto (fun n => ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2) atTop (𝓝 0) := by
    simpa only [toLp_sub_norm_sq] using hlim
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    dist_eq_norm] using hroot

theorem cutoffMode_value_integral_tendsto :
    Tendsto (fun n => ∫ x, ‖(cutoffMode n).val x - planarResolventMode x‖ ^ 2)
      atTop (𝓝 0) := by
  have h : Tendsto (fun n => ∫ x, ‖(cutoffMode n).val x - planarResolventMode x‖ ^ 2)
      atTop (𝓝 (∫ _ : PlanarPosition, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun x => planarResolventMode x ^ 2)
    · intro n
      exact (((cutoffMode n).property.1.continuous.sub
        planarResolventMode_C7.continuous).norm.pow 2).aestronglyMeasurable
    · exact mode_square_integrable
    · intro n
      filter_upwards [] with x
      change ‖‖(cutoffMode n).val x - planarResolventMode x‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, sq_abs]
      change (cutoff n x * planarResolventMode x - planarResolventMode x) ^ 2 ≤ _
      have ha := mul_nonneg (cutoff_nonnegative n x) (planarResolventMode_positive x).le
      have hb := mul_le_of_le_one_left (planarResolventMode_positive x).le (cutoff_le_one n x)
      have hab := mul_nonneg ha (sub_nonneg.mpr hb)
      nlinarith
    · filter_upwards [] with x
      change Tendsto (fun n => ‖cutoff n x * planarResolventMode x - planarResolventMode x‖ ^ 2)
        atTop (𝓝 0)
      have hlim := ((cutoff_tendsto x).mul_const (planarResolventMode x)).sub
        (tendsto_const_nhds (x := planarResolventMode x))
      simpa only [one_mul, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        hlim.norm.pow 2
  simpa only [integral_zero] using h

theorem cutoffMode_grad_integral_tendsto :
    Tendsto (fun n => ∫ x, ‖grad (cutoffMode n).val x - grad planarResolventMode x‖ ^ 2)
      atTop (𝓝 0) := by
  have hi : Integrable (fun x => 8 * ‖grad planarResolventMode x‖ ^ 2 +
      2 * cutoffGradBound ^ 2 * planarResolventMode x ^ 2) :=
    (mode_grad_square_integrable.const_mul 8).add
      (mode_square_integrable.const_mul (2 * cutoffGradBound ^ 2))
  have h : Tendsto (fun n => ∫ x, ‖grad (cutoffMode n).val x - grad planarResolventMode x‖ ^ 2)
      atTop (𝓝 (∫ _ : PlanarPosition, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => 8 * ‖grad planarResolventMode x‖ ^ 2 +
        2 * cutoffGradBound ^ 2 * planarResolventMode x ^ 2)
    · intro n
      exact (((continuous_grad (cutoffMode n).property.1).sub
        (continuous_grad (planarResolventMode_C7.of_le (by norm_num)))).norm.pow 2).aestronglyMeasurable
    · exact hi
    · intro n
      filter_upwards [] with x
      change ‖‖grad (cutoffMode n).val x - grad planarResolventMode x‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb : ‖grad (cutoffMode n).val x - grad planarResolventMode x‖ ≤
          2 * ‖grad planarResolventMode x‖ + cutoffGradBound * ‖planarResolventMode x‖ := by
        apply (norm_sub_le _ _).trans
        rw [cutoffMode_grad]
        have ha := norm_add_le (cutoff n x • grad planarResolventMode x)
          (planarResolventMode x • grad (cutoff n) x)
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonnegative n x)] at ha
        have h₁ := mul_le_of_le_one_left (norm_nonneg (grad planarResolventMode x))
          (cutoff_le_one n x)
        have h₂ := mul_le_mul_of_nonneg_left (cutoff_grad_bound n x) (norm_nonneg (planarResolventMode x))
        nlinarith
      have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      have hs := sq_nonneg (2 * ‖grad planarResolventMode x‖ - cutoffGradBound * ‖planarResolventMode x‖)
      simp only [Real.norm_eq_abs, abs_of_pos (planarResolventMode_positive x)] at hb2 hs
      nlinarith
    · filter_upwards [] with x
      have hlim := (cutoffMode_grad_tendsto x).sub
        (tendsto_const_nhds (x := grad planarResolventMode x))
      simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hlim.norm.pow 2
  simpa only [integral_zero] using h

def modeTarget : Target := ⟨mode_memLp.toLp planarResolventMode,
  mode_grad_memLp.toLp (grad planarResolventMode)⟩

theorem cutoffMode_graph_tendsto :
    Tendsto (fun n => graph (μ := volume) (cutoffMode n)) atTop (𝓝 modeTarget) := by
  have hval := toLp_tendsto_of_integral_sub_sq
    (fun n => memLp_of_mem_C1c (μ := volume) (cutoffMode n).property) mode_memLp
      cutoffMode_value_integral_tendsto
  have hgrad := toLp_tendsto_of_integral_sub_sq
    (fun n => memLp_grad_of_mem_C1c (μ := volume) (cutoffMode n).property) mode_grad_memLp
      cutoffMode_grad_integral_tendsto
  exact hval.prodMk_nhds hgrad

theorem modeTarget_mem : modeTarget ∈ Sobolev := by
  apply (isClosed_h1 (μ := volume) (E := PlanarPosition)).mem_of_tendsto cutoffMode_graph_tendsto
  exact Filter.Eventually.of_forall (fun n => subset_closure
    (show graph (μ := volume) (cutoffMode n) ∈
      (LinearMap.range (graph (μ := volume) (E := PlanarPosition)) : Set Target) from
        ⟨cutoffMode n, rfl⟩))

/-- The positive resolvent mode belongs to the closed H¹ graph. -/
def mode : Sobolev := ⟨modeTarget, modeTarget_mem⟩

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
