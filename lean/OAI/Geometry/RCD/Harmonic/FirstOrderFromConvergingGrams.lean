import OAI.Geometry.RCD.Harmonic.NearbyMeanGrams
import OAI.Geometry.RCD.Coordinates.SplittingApproximation

namespace OAI

/-! # Converging Gram errors give splitting for the prescribed original family -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem NoncollapsedRCD.first_order_of_converging_grams {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X)
    (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hrep : ∀ k i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k i) =ᵐ[
      (hausdorff n X).restrict (ball (p k) (r k))] fun x => v k x i)
    (hv : ∀ k, ContinuousOn (v k) (ball (p k) (r k)))
    (hu : ∀ k i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (r k)) (u k i))
    {C : ℝ} (hC : 1 ≤ C)
    (hvol : ∀ k, (hausdorff n X).real (ball (p k) (2*r k)) ≤
      C*(hausdorff n X).real (ball (p k) (r k)))
    (hgrad : ∀ i : Fin n, ∀ β : ℝ, 0 < β → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (3*r k)),
        localGamma (hausdorff n X) hX.quadratic (u k i) (u k i) x ≤ 1+β)
    (hgram : ∀ i j : Fin n, Tendsto (fun k => ((hausdorff n X).real (ball (p k) (2*r k)))⁻¹*
      ∫ x in ball (p k) (2*r k),
        |localGamma (hausdorff n X) hX.quadratic (u k i) (u k j) x-(if i=j then 1 else 0)|
        ∂hausdorff n X) atTop (𝓝 0)) :
    ∀ β : ℝ, 0 < β → ∀ᶠ k in atTop,
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic (p k) (r k) β (u k) (v k) := by
  let μ := hausdorff n X
  intro β hβ
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hg : ∀ᶠ k in atTop, ∀ i : Fin n,
      ∀ᵐ x ∂μ.restrict (ball (p k) (3*r k)),
        localGamma μ hX.quadratic (u k i) (u k i) x ≤ 1+β :=
    eventually_all.mpr (fun i => hgrad i β hβ)
  have he : ∀ᶠ k in atTop, ∀ i j : Fin n,
      (μ.real (ball (p k) (2*r k)))⁻¹*(∫ x in ball (p k) (2*r k),
        |localGamma μ hX.quadratic (u k i) (u k j) x-(if i=j then 1 else 0)| ∂μ) ≤ β/C := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    exact ((hgram i j).eventually (eventually_lt_nhds (div_pos hβ hC0))).mono (fun _ h => h.le)
  filter_upwards [hg,he] with k hgk hek
  refine ⟨hrep k,hv k,hu k,?_,?_⟩
  · intro i
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith [hr k] : r k ≤ 3*r k)) (hgk i)] with x hx
    exact hx.trans (by nlinarith : 1+β ≤ (1+β)^2)
  · intro i j
    have hzero (a : ℝ) (ha : 0 < a) : 0 < μ.real (ball (p k) (a*r k)) :=
      ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos ha (hr k))).ne'
        (hX.finiteOnBounded _ isBounded_ball).ne
    have hfinite : μ (ball (p k) (2*r k)) ≠ ⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
    have hh := average_nonneg_le_of_subset μ
      (ball_subset_ball (by linarith [hr k] : r k ≤ 2*r k))
      (by simpa only [one_mul] using hzero 1 zero_lt_one) (hzero 2 (by norm_num))
      (((localGamma_memL1 μ hX.quadratic (u k i) (u k j)).integrableOn.sub
        (integrableOn_const hfinite)).abs)
      (fun x => abs_nonneg (localGamma μ hX.quadratic (u k i) (u k j) x-(if i=j then 1 else 0)))
      (div_nonneg hβ.le hC0.le) (hvol k) (hek i j)
    exact hh.trans_eq (by field_simp)

end RegularPointCoordinates

end

end OAI
