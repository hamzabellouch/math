import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLocalConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Smooth spatial filtering preserves local uniform limits

A globally bounded sequence that vanishes locally uniformly also vanishes,
on every fixed ball, after convolution by a Schwartz kernel. The proof
uses the compact-ball Banach space, so the conclusion is uniform in space.
-/

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def shiftedBallRestriction (R : ℝ) (u : C(E, ℂ)) (z : E) :
    C(Metric.closedBall (0 : E) R, ℂ) where
  toFun y := u (y - z)
  continuous_toFun := u.continuous.comp (continuous_subtype_val.sub continuous_const)

@[simp] theorem shiftedBallRestriction_apply (R : ℝ) (u : C(E, ℂ)) (z : E)
    (y : Metric.closedBall (0 : E) R) : shiftedBallRestriction R u z y = u (y - z) := rfl

theorem continuous_shiftedBallRestriction (R : ℝ) (u : C(E, ℂ)) :
    Continuous (shiftedBallRestriction R u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact u.continuous.comp ((continuous_subtype_val.comp continuous_snd).sub continuous_fst)

theorem shiftedBallRestriction_norm_le (R M : ℝ) (hM : 0 ≤ M) (u : C(E, ℂ))
    (hu : ∀ y : E, ‖u y‖ ≤ M) (z : E) : ‖shiftedBallRestriction R u z‖ ≤ M := by
  apply (ContinuousMap.norm_le _ hM).mpr
  intro y
  exact hu _

noncomputable def schwartzBallConvolution (R : ℝ) (K : 𝓢(E, ℂ)) (u : C(E, ℂ)) :
    C(Metric.closedBall (0 : E) R, ℂ) :=
  ∫ z : E, K z • shiftedBallRestriction R u z

theorem schwartzBallConvolution_integrable (R M : ℝ) (hM : 0 ≤ M)
    (K : 𝓢(E, ℂ)) (u : C(E, ℂ)) (hu : ∀ y : E, ‖u y‖ ≤ M) :
    Integrable (fun z : E => K z • shiftedBallRestriction R u z) := by
  apply (K.integrable.norm.mul_const M).mono'
    ((K.continuous.smul (continuous_shiftedBallRestriction R u)).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖K z • shiftedBallRestriction R u z‖ ≤ ‖K z‖ * M
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (shiftedBallRestriction_norm_le R M hM u hu z) (norm_nonneg _)

theorem schwartzBallConvolution_apply (R M : ℝ) (hM : 0 ≤ M)
    (K : 𝓢(E, ℂ)) (u : C(E, ℂ)) (hu : ∀ y : E, ‖u y‖ ≤ M)
    (y : Metric.closedBall (0 : E) R) :
    schwartzBallConvolution R K u y = ∫ z : E, K z * u (y - z) := by
  have h := (ContinuousMap.evalCLM (R := ℂ) y).integral_comp_comm
    (schwartzBallConvolution_integrable R M hM K u hu)
  exact h.symm

theorem tendsto_schwartzBallConvolution_zero (R M : ℝ) (hM : 0 ≤ M)
    (K : 𝓢(E, ℂ)) (u : ℕ → C(E, ℂ)) (hu : ∀ n y, ‖u n y‖ ≤ M)
    (hlocal : ∀ S ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ S → ‖u n y‖ < ε) :
    Tendsto (fun n => schwartzBallConvolution R K (u n)) atTop (𝓝 0) := by
  have hshift (z : E) : Tendsto (fun n => shiftedBallRestriction R (u n) z) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_order.2
    constructor
    · intro r hr
      exact Eventually.of_forall (fun n => hr.trans_le (norm_nonneg _))
    · intro ε hε
      filter_upwards [hlocal (R + ‖z‖) (ε / 2) (half_pos hε)] with n hn
      have hb : ‖shiftedBallRestriction R (u n) z‖ ≤ ε / 2 := by
        apply (ContinuousMap.norm_le _ (half_pos hε).le).mpr
        intro y
        apply (hn _ ?_).le
        have hy : ‖(y : E)‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using y.property
        exact (norm_sub_le (y : E) z).trans (add_le_add hy le_rfl)
      exact hb.trans_lt (half_lt_self hε)
  have hpoint (z : E) : Tendsto (fun n => K z • shiftedBallRestriction R (u n) z) atTop (𝓝 0) := by
    have hz : K z • (0 : C(Metric.closedBall (0 : E) R, ℂ)) = 0 := by
      ext y
      change K z * 0 = 0
      exact mul_zero _
    simpa only [hz] using (hshift z).const_smul (K z)
  have hbound (n : ℕ) : ∀ᵐ z : E,
      ‖K z • shiftedBallRestriction R (u n) z‖ ≤ ‖K z‖ * M := by
    filter_upwards [] with z
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (shiftedBallRestriction_norm_le R M hM (u n) (hu n) z) (norm_nonneg _)
  simpa only [schwartzBallConvolution, integral_zero] using
    tendsto_integral_of_dominated_convergence (fun z : E => ‖K z‖ * M)
      (fun n => (schwartzBallConvolution_integrable R M hM K (u n) (hu n)).aestronglyMeasurable)
      (K.integrable.norm.mul_const M) hbound (ae_of_all _ hpoint)

theorem schwartzBallConvolution_sub (R M M₀ : ℝ) (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀)
    (K : 𝓢(E, ℂ)) (u v : C(E, ℂ))
    (hu : ∀ y, ‖u y‖ ≤ M) (hv : ∀ y, ‖v y‖ ≤ M₀) :
    schwartzBallConvolution R K (u - v) =
      schwartzBallConvolution R K u - schwartzBallConvolution R K v := by
  unfold schwartzBallConvolution
  rw [← integral_sub (schwartzBallConvolution_integrable R M hM K u hu)
    (schwartzBallConvolution_integrable R M₀ hM₀ K v hv)]
  apply integral_congr_ae
  filter_upwards [] with z
  ext y
  change K z * (u (y - z) - v (y - z)) = K z * u (y - z) - K z * v (y - z)
  ring

theorem tendsto_schwartzBallConvolution (R M M₀ : ℝ) (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀)
    (K : 𝓢(E, ℂ)) (u : ℕ → C(E, ℂ)) (v : C(E, ℂ))
    (hu : ∀ n y, ‖u n y‖ ≤ M) (hv : ∀ y, ‖v y‖ ≤ M₀)
    (hlocal : ∀ S ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ S → ‖u n y - v y‖ < ε) :
    Tendsto (fun n => schwartzBallConvolution R K (u n)) atTop
      (𝓝 (schwartzBallConvolution R K v)) := by
  have hb (n : ℕ) (y : E) : ‖(u n - v) y‖ ≤ M + M₀ :=
    (norm_sub_le _ _).trans (add_le_add (hu n y) (hv y))
  have hz := tendsto_schwartzBallConvolution_zero R (M + M₀) (add_nonneg hM hM₀)
    K (fun n => u n - v) hb hlocal
  have he (n : ℕ) := schwartzBallConvolution_sub R M M₀ hM hM₀ K (u n) v (hu n) hv
  simp_rw [he] at hz
  simpa only [sub_add_cancel, zero_add] using hz.add_const (schwartzBallConvolution R K v)

end DefocusingNLS

end OAI
