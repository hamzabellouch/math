import OAI.Geometry.EinsteinFour.ContinuousFieldDerivative
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

/-! Integration by parts from invariance of the frame-flow measure. The
only derivative hypotheses concern individual continuous fields along
the flow; the weighted identity is derived using the product rule. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

local instance flowGreenNormedAddCommGroup : NormedAddCommGroup C(Ω, ℝ) :=
  ContinuousMap.instNormedAddCommGroup
local instance flowGreenNormedSpace : NormedSpace ℝ C(Ω, ℝ) :=
  ContinuousMap.normedSpace

private def fieldIntegral : C(Ω, ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM (μ := μ)).comp (ContinuousMap.toLp 1 μ ℝ)

private theorem fieldIntegral_apply (f : C(Ω, ℝ)) :
    fieldIntegral μ f = ∫ x, f x ∂μ := by
  change L1.integralCLM (ContinuousMap.toLp 1 μ ℝ f) = _
  rw [← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) μ f)

/-- The integral of a continuous infinitesimal generator is zero. This
is obtained by differentiating the invariant integral, not assumed as
a separate integration-by-parts law. -/
theorem integral_flow_derivative_zero
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hμ : ∀ t, MeasurePreserving (φ t) μ μ)
    (f d : C(Ω, ℝ))
    (hd : ∀ t x, HasDerivAt (fun s => f (φ s x)) (d (φ t x)) t) :
    (∫ x, d x ∂μ) = 0 := by
  let F : ℝ → C(Ω, ℝ) := fun t =>
    ⟨fun x => f (φ t x), f.continuous.comp
      (hφ.comp (continuous_const.prodMk continuous_id))⟩
  let G : ℝ → C(Ω, ℝ) := fun t =>
    ⟨fun x => d (φ t x), d.continuous.comp
      (hφ.comp (continuous_const.prodMk continuous_id))⟩
  have hcurve : HasDerivAt F (G 0) 0 :=
    continuousField_hasDerivAt_of_joint (d.continuous.comp hφ) hd 0
  have hi := (fieldIntegral μ).hasFDerivAt.comp_hasDerivAt 0 hcurve
  change HasDerivAt (fun t => fieldIntegral μ (F t)) (fieldIntegral μ (G 0)) 0 at hi
  have hs (t : ℝ) : fieldIntegral μ (F t) = ∫ x, f x ∂μ := by
    rw [fieldIntegral_apply]
    exact (hμ t).integral_comp' f
  have hz : fieldIntegral μ (G 0) = ∫ x, d x ∂μ := by
    rw [fieldIntegral_apply]
    exact (hμ 0).integral_comp' d
  have hi' : HasDerivAt (fun _ : ℝ => ∫ x, f x ∂μ) (∫ x, d x ∂μ) 0 := by
    simpa only [hs, hz] using hi
  exact hi'.unique (hasDerivAt_const 0 (∫ x, f x ∂μ))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Weighted Green identity for any two tensor-coordinate fields along a
measure-preserving parallel-frame flow. -/
theorem weighted_flow_green
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hμ : ∀ t, MeasurePreserving (φ t) μ μ)
    (m dm : C(Ω, ℝ)) (f df g dg : C(Ω, E))
    (hm : ∀ t x, HasDerivAt (fun s => m (φ s x)) (dm (φ t x)) t)
    (hf : ∀ t x, HasDerivAt (fun s => f (φ s x)) (df (φ t x)) t)
    (hg : ∀ t x, HasDerivAt (fun s => g (φ s x)) (dg (φ t x)) t) :
    (∫ x, m x * inner ℝ (df x) (g x) +
      dm x * inner ℝ (f x) (g x) ∂μ) =
      -(∫ x, m x * inner ℝ (f x) (dg x) ∂μ) := by
  let P : C(Ω, ℝ) := ⟨fun x => m x * inner ℝ (f x) (g x), by fun_prop⟩
  let D : C(Ω, ℝ) := ⟨fun x =>
    m x * inner ℝ (df x) (g x) + dm x * inner ℝ (f x) (g x) +
      m x * inner ℝ (f x) (dg x), by fun_prop⟩
  have hD (t : ℝ) (x : Ω) :
      HasDerivAt (fun s => P (φ s x)) (D (φ t x)) t := by
    convert (hm t x).mul ((hf t x).inner ℝ (hg t x)) using 1
    dsimp [P, D]
    ring
  have hz := integral_flow_derivative_zero μ φ hφ hμ P D hD
  have hfirst : Integrable
      (fun x => m x * inner ℝ (df x) (g x) + dm x * inner ℝ (f x) (g x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlast : Integrable (fun x => m x * inner ℝ (f x) (dg x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ x, (m x * inner ℝ (df x) (g x) + dm x * inner ℝ (f x) (g x)) +
    m x * inner ℝ (f x) (dg x) ∂μ) = 0 at hz
  rw [integral_add hfirst hlast] at hz
  linarith

/-- Sum the four parallel-frame directions. This is the weighted rough
Laplacian identity used for the covariant Weyl gradient. -/
theorem weighted_four_direction_green
    (φ : Fin 4 → ℝ → Ω ≃ᵐ Ω)
    (hφ : ∀ i, Continuous (fun p : ℝ × Ω => φ i p.1 p.2))
    (hμ : ∀ i t, MeasurePreserving (φ i t) μ μ)
    (m : C(Ω, ℝ)) (dm : Fin 4 → C(Ω, ℝ))
    (f : C(Ω, E)) (df ddf : Fin 4 → C(Ω, E))
    (hm : ∀ i t x, HasDerivAt (fun s => m (φ i s x)) (dm i (φ i t x)) t)
    (hf : ∀ i t x, HasDerivAt (fun s => f (φ i s x)) (df i (φ i t x)) t)
    (hdf : ∀ i t x, HasDerivAt (fun s => df i (φ i s x)) (ddf i (φ i t x)) t) :
    (∫ x, m x * (∑ i, ‖df i x‖ ^ 2) +
      ∑ i, dm i x * inner ℝ (f x) (df i x) ∂μ) =
      -(∫ x, m x * inner ℝ (f x) (∑ i, ddf i x) ∂μ) := by
  have hleft (i : Fin 4) : Integrable
      (fun x => m x * inner ℝ (df i x) (df i x) +
        dm i x * inner ℝ (f x) (df i x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hright (i : Fin 4) : Integrable
      (fun x => m x * inner ℝ (f x) (ddf i x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum :
      (∫ x, ∑ i, (m x * inner ℝ (df i x) (df i x) +
        dm i x * inner ℝ (f x) (df i x)) ∂μ) =
      -(∫ x, ∑ i, m x * inner ℝ (f x) (ddf i x) ∂μ) := by
    rw [integral_finsetSum _ (fun i _ => hleft i),
      integral_finsetSum _ (fun i _ => hright i)]
    simp_rw [weighted_flow_green μ _ (hφ _) (hμ _) m (dm _) f (df _) (df _) (ddf _)
      (hm _) (hf _) (hdf _)]
    simp only [Finset.sum_neg_distrib]
  simpa only [real_inner_self_eq_norm_sq, Finset.sum_add_distrib,
    Finset.mul_sum, inner_sum] using hsum

end

end PositiveEinsteinFour.Averages

end OAI
