import OAI.Geometry.RCD.Harmonic.HarmonicLinearRecovery
import OAI.Geometry.RCD.Sobolev.HarmonicEnergyTailSequence
import OAI.Geometry.RCD.Sobolev.ScaledGammaExcess

namespace OAI

/-! # Sharp gradients for the actual harmonic sequence with a unit linear limit -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_linear_sharp {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1≤K*r k^2) (hcurv5 : ∀ k, -1≤K*(5*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w k))
    {M : ℝ} (hM : 0<M) (hnorm : ∀ k, harmonicTargetNorm hX (p k) (5*r k) (w k)≤M)
    (L : Euclidean n →L[ℝ] ℝ) (hL : ‖L‖≤1)
    (hconv : ∀ W, 0<W → W<5 → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-L (V k x)|≤δ) :
    ∀ β : ℝ, 0<β → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (3*r k)),
        r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤1+β := by
  obtain ⟨N,q,⟨B,hB,hbound⟩,hq,hstrong⟩ := hX.harmonic_linear_recovery hn
    p r ε V hr hcurv hε hε1 hεlim hV w hw hM hnorm L hL hconv
  let μ := hausdorff n X
  let Ω := fun k => ball (p (k+N)) (4*r (k+N))
  let mass := fun k => μ.real (ball (p (k+N)) (5*r (k+N)))
  have : ∀ k, IsFiniteMeasure (μ.restrict (Ω k)) := fun k =>
    ⟨by simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded (Ω k) isBounded_ball⟩
  have hm (k : ℕ) : 0 < mass k := ENNReal.toReal_pos
    (hX.fullSupport _ _ (mul_pos (by norm_num) (hr (k+N)))).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hmass (k : ℕ) : (mass k)⁻¹*μ.real (Ω k)≤1 := by
    have hle : μ.real (Ω k)≤ mass k := ENNReal.toReal_mono
      (hX.finiteOnBounded _ isBounded_ball).ne
      (measure_mono (ball_subset_ball (mul_le_mul_of_nonneg_right (by norm_num : (4:ℝ)≤5) (hr (k+N)).le)))
    exact (mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (hm k).le)).trans_eq (inv_mul_cancel₀ (hm k).ne')
  have hstrong' : Tendsto (fun k => (mass k)⁻¹*r (k+N)^2*∫ x in Ω k,
      localGamma μ hX.quadratic (w (k+N)-q k) (w (k+N)-q k) x ∂μ) atTop (𝓝 0) := by
    convert hstrong using 1
    funext k
    dsimp only [mass,Ω,μ]
    ring
  have htail := scaled_gamma_excess_tendsto μ hX.quadratic Ω (fun k => r (k+N))
    (fun k => (mass k)⁻¹) (fun k => hr (k+N)) (fun k => inv_nonneg.mpr (hm k).le) hmass
    (Real.sqrt_nonneg B) (fun k => w (k+N)) q
    (Eventually.of_forall (fun k => by simpa only [Real.sq_sqrt hB] using hbound k)) hq hstrong'
  have hsharp := hX.harmonic_energy_tail_sequence hn (fun k => p (k+N)) (fun k => r (k+N))
    (fun k => hr (k+N)) (fun k => hcurv5 (k+N)) (fun k => w (k+N))
    (fun k => hw (k+N)) hB hbound htail
  intro β hβ
  obtain ⟨j,hj⟩ := eventually_atTop.mp (hsharp β hβ)
  filter_upwards [eventually_ge_atTop (j+N)] with k hk
  have hh := hj (k-N) (by omega)
  simpa only [Nat.sub_add_cancel (show N≤k by omega)] using hh

end RegularPointCoordinates

end

end OAI
