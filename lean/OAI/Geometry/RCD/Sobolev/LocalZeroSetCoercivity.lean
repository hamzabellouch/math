import OAI.Geometry.RCD.Transport.TransportPoincare

namespace OAI

/-! # Local coercivity for functions with a large zero set

The zero set controls the constant in the local Poincare estimate. This
is the local ingredient for the support-sensitive Sobolev estimate.
-/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

private theorem integral_sq_le_six_variance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {Ω B : Set X} (hfin : μ Ω ≠ ∞) (hsub : B ⊆ Ω) (hhalf : μ.real Ω ≤ 2*μ.real B)
    (u : Lp ℝ 2 μ) (hz : u =ᵐ[μ.restrict B] 0) (k : ℝ) :
    (∫ x in Ω, u x ^ 2 ∂μ) ≤ 6 * ∫ x in Ω, (u x-k)^2 ∂μ := by
  let : IsFiniteMeasure (μ.restrict Ω) := ⟨by simpa using hfin.lt_top⟩
  have hu : MemLp u 2 (μ.restrict Ω) := (Lp.memLp u).mono_measure Measure.restrict_le_self
  have hv : Integrable (fun x => (u x-k)^2) (μ.restrict Ω) :=
    (hu.sub (memLp_const k)).integrable_sq
  have hbound : k^2 * μ.real B ≤ ∫ x in Ω, (u x-k)^2 ∂μ := by
    calc
      _ = ∫ x in B, (u x-k)^2 ∂μ := by
        rw [integral_congr_ae (show (fun x => (u x-k)^2) =ᵐ[μ.restrict B]
          fun _ => k^2 from hz.mono (fun x hx => by simp [hx]))]
        simp [mul_comm]
      _ ≤ _ := setIntegral_mono_set hv (Filter.Eventually.of_forall (fun x => sq_nonneg (u x-k)))
        (Filter.Eventually.of_forall hsub)
  have hk : k^2 * μ.real Ω ≤ 2 * ∫ x in Ω, (u x-k)^2 ∂μ := by
    have hh := mul_le_mul_of_nonneg_left hhalf (sq_nonneg k)
    nlinarith
  have hpoint : (∫ x in Ω, u x^2 ∂μ) ≤
      ∫ x in Ω, (2*(u x-k)^2 + 2*k^2) ∂μ := by
    apply integral_mono_ae hu.integrable_sq ((hv.const_mul 2).add (integrable_const _))
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Pi.add_apply, Pi.sub_apply]
      nlinarith [sq_nonneg (u x-2*k)]
  rw [integral_add (hv.const_mul 2) (integrable_const _), integral_const_mul] at hpoint
  simp only [integral_const, smul_eq_mul, Measure.real] at hpoint
  change (∫ x in Ω, u x^2 ∂μ) ≤
    2*(∫ x in Ω, (u x-k)^2 ∂μ) + (μ.restrict Ω Set.univ).toReal*(2*k^2) at hpoint
  rw [Measure.restrict_apply_univ] at hpoint
  change (∫ x in Ω, u x^2 ∂μ) ≤
    2*(∫ x in Ω, (u x-k)^2 ∂μ) + μ.real Ω*(2*k^2) at hpoint
  nlinarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Under bounded rescaled curvature, a zero set occupying at least half
of the ball removes the additive constant, uniformly in its center. -/
theorem NoncollapsedRCD.local_zero_set_coercivity {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : X) (r : ℝ), 0 < r → -κ ≤ K*r^2 →
      ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
      ∀ B : Set X, MeasurableSet B → B ⊆ ball p r →
      (hausdorff n X).real (ball p r) ≤ 2*(hausdorff n X).real B →
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[
        (hausdorff n X).restrict B] 0) →
      (∫ x in ball p r, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x)^2
        ∂hausdorff n X) ≤ C*r^2 *
        ∫ x in ball p (8*r), localGamma (hausdorff n X) hX.quadratic w w x
          ∂hausdorff n X := by
  obtain ⟨C, hC, hP⟩ := hX.localMeanPoincareInput hn κ hκ
  refine ⟨6*C^2, by positivity, ?_⟩
  intro p r hr hcurv w B _hB hsub hhalf hz
  obtain ⟨k, hk⟩ := hP p r hr hcurv w
  have h := integral_sq_le_six_variance (hausdorff n X)
    (hX.finiteOnBounded _ isBounded_ball).ne hsub hhalf
    (SobolevSpace.toLp (hausdorff n X) hX.quadratic w) hz k
  calc
    _ ≤ 6 * ∫ x in ball p r,
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x-k)^2 ∂hausdorff n X := h
    _ ≤ 6*((C*r)^2 * ∫ x in ball p (8*r),
        localGamma (hausdorff n X) hX.quadratic w w x ∂hausdorff n X) :=
      mul_le_mul_of_nonneg_left hk (by norm_num)
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
