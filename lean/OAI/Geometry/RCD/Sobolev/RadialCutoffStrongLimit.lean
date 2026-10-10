import OAI.Geometry.RCD.Sobolev.BoundedLocalBochner

namespace OAI

/-! # Strong radial cutoff convergence for bounded Sobolev functions -/

open Set Filter Metric MeasureTheory
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem integral_outer_ball_tendsto_zero (p : X) {f : X → ℝ} (hf : Integrable f μ) :
    Tendsto (fun k : ℕ => ∫ x in {x | (k:ℝ)+1 ≤ dist p x}, f x ∂μ) atTop (𝓝 0) := by
  let S (k : ℕ) := {x : X | (k:ℝ)+1 ≤ dist p x}
  have hS (k : ℕ) : MeasurableSet (S k) :=
    (isClosed_le continuous_const (continuous_const.dist continuous_id)).measurableSet
  have hanti : Antitone S := by
    intro i j hij x hx
    have hij' : (i:ℝ)+1≤(j:ℝ)+1 :=
      add_le_add (show (i:ℝ)≤(j:ℝ) by exact_mod_cast hij) le_rfl
    exact hij'.trans hx
  have hEmpty : (⋂ k, S k)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨k,hk⟩ := exists_nat_gt (dist p x)
    have h := mem_iInter.mp hx k
    change (k:ℝ)+1 ≤ dist p x at h
    linarith
  simpa only [hEmpty,Measure.restrict_empty,integral_zero_measure] using
    tendsto_setIntegral_of_antitone hS hanti ⟨0,hf.integrableOn⟩

theorem SobolevSpace.radial_cutoff_strong_limit [IsFiniteMeasureOnCompacts μ]
    (u : SobolevSpace μ hQ) (C : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x|≤C) (p : X) :
    Tendsto (fun k : ℕ => SobolevSpace.product μ hQ
      (radialSobolevCutoff μ hQ p (by positivity : 0<(k:ℝ)+1)) u 1 C) atTop (𝓝 u) := by
  let U (k : ℕ) := SobolevSpace.product μ hQ
    (radialSobolevCutoff μ hQ p (by positivity : 0<(k:ℝ)+1)) u 1 C
  let a (k : ℕ) := ∫ x in {x | (k:ℝ)+1 ≤ dist p x}, (SobolevSpace.toLp μ hQ u x)^2 ∂μ
  let b (k : ℕ) := ∫ x in {x | (k:ℝ)+1 ≤ dist p x}, (SobolevSpace.minimalSlope μ hQ u x)^2 ∂μ
  have ha := integral_outer_ball_tendsto_zero μ p (Lp.memLp (SobolevSpace.toLp μ hQ u)).integrable_sq
  have hb := integral_outer_ball_tendsto_zero μ p (Lp.memLp (SobolevSpace.minimalSlope μ hQ u)).integrable_sq
  have he (k : ℕ) : ‖U k-u‖^2 ≤ 3*a k+2*b k := by
    have h := SobolevSpace.radial_cutoff_error_norm_sq μ hQ u C hu p
      (by positivity : 0<(k:ℝ)+1)
    rw [norm_sub_rev] at h
    have hr : 1≤((k:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hdiv : 2/((k:ℝ)+1)^2 ≤ 2 :=
      (div_le_iff₀ (by positivity : 0<((k:ℝ)+1)^2)).mpr (by linarith)
    have ha0 : 0≤a k := integral_nonneg fun x => sq_nonneg _
    change ‖U k-u‖^2 ≤ _ at h ⊢
    nlinarith only [h,mul_nonneg (show 0≤2-2/((k:ℝ)+1)^2 by linarith) ha0]
  have hz : Tendsto (fun k => ‖U k-u‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun k => sq_nonneg _) he (by
      simpa only [mul_zero,add_zero] using (ha.const_mul 3).add (hb.const_mul 2))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hz.sqrt

end RegularPointCoordinates

end

end OAI
