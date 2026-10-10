import OAI.Geometry.RCD.Sobolev.RadialCutoffStrongLimit

namespace OAI

/-! # Global Bochner tests for bounded regular functions

Radial cutoff convergence removes the support restriction. The source is
only required to belong to the actual Sobolev space.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bounded_global_bochner {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (p : X)
    (u d G w : SobolevSpace (hausdorff n X) hX.quadratic)
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic d))
    (v : X → ℝ) {L : ℝ≥0} (hv : LipschitzWith L v)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] v)
    (A : ℝ≥0)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x|≤A)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic u u)
    (q : X → ℝ) (hq : Continuous q) (C : ℝ≥0) (hqC : ∀ x, |q x|≤C)
    (hq0 : ∀ x, 0≤q x)
    (hw : SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[hausdorff n X] q) :
    0≤bochnerTestForm (hausdorff n X) hX.quadratic (-K) G w-
      weightedGamma (hausdorff n X) hX.quadratic
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic w) u d := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let W (k : ℕ) := SobolevSpace.product μ Q
    (radialSobolevCutoff μ Q p (by positivity : 0<(k:ℝ)+1)) w 1 C
  have hwb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q w x|≤C := by
    filter_upwards [hw] with x hx
    change SobolevSpace.toLp μ Q w x=q x at hx
    rw [hx]
    exact hqC x
  have hconv : Tendsto W atTop (𝓝 w) := SobolevSpace.radial_cutoff_strong_limit μ Q w C hwb p
  have hpos (k : ℕ) : 0≤bochnerTestForm μ Q (-K) G (W k)-
      weightedGamma μ Q (SobolevSpace.toLp μ Q (W k)) u d := by
    let r : ℝ := (k:ℝ)+1
    have hr : 0<r := by positivity
    let z : X → ℝ := fun x => radialCutoff p r x*q x
    have hzc : Continuous z := (radialCutoff_lipschitz p hr).continuous.mul hq
    have hzs : HasCompactSupport z := (radialCutoff_hasCompactSupport p hr).mul_right
    let zB : X →ᵇ ℝ := ofCompactSupport z hzc hzs
    have hηb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (radialSobolevCutoff μ Q p hr) x|≤(1:ℝ≥0) := by
      filter_upwards [radialSobolevCutoff_coe μ Q p hr] with x hx
      rw [hx,abs_of_nonneg (radialCutoff_bounds p r x).1]
      exact (radialCutoff_bounds p r x).2
    have hWr : SobolevSpace.toLp μ Q (W k) =ᵐ[μ] zB := by
      filter_upwards [SobolevSpace.product_coe μ Q (radialSobolevCutoff μ Q p hr) w 1 C hηb hwb,
        radialSobolevCutoff_coe μ Q p hr,hw] with x hx hy hz
      exact hx.trans (by rw [hy,hz]; rfl)
    obtain ⟨R,hR,hzsR⟩ := hzs.isBounded.subset_ball_lt 0 p
    have ht := hX.bounded_local_bochner hn u d G (W k) (SobolevSpace.toLp μ Q d)
      hd v hv hu A hA hG p hR (EventuallyEq.refl _ _) zB hzsR
      (fun x => mul_nonneg (radialCutoff_bounds p r x).1 (hq0 x)) hWr
    have he : weightedGamma μ Q (SobolevSpace.toLp μ Q (W k)) u d =
        ∫ x, zB x*localGamma μ Q u d x ∂μ :=
      integral_congr_ae (hWr.mono fun x hx => congrArg (fun a => a*localGamma μ Q u d x) hx)
    rwa [←he] at ht
  have hΓ := localGamma_memLp_of_bounded_gradient μ Q u d L
    (SobolevSpace.minimalSlope_le_lipschitz μ Q u hv hu)
  have hE := (energyForm_continuous μ Q).tendsto (G,w) |>.comp (tendsto_const_nhds.prodMk_nhds hconv)
  have hW := (SobolevSpace.toLpCLM μ Q).continuous.tendsto w |>.comp hconv
  have hI : Tendsto (fun k => inner ℝ (SobolevSpace.toLp μ Q (W k)) (SobolevSpace.toLp μ Q G))
      atTop (𝓝 (inner ℝ (SobolevSpace.toLp μ Q w) (SobolevSpace.toLp μ Q G))) :=
    hW.inner tendsto_const_nhds
  have hJ : Tendsto (fun k => weightedGamma μ Q (SobolevSpace.toLp μ Q (W k)) u d)
      atTop (𝓝 (weightedGamma μ Q (SobolevSpace.toLp μ Q w) u d)) := by
    simp only [weightedGamma_eq_L2_inner μ Q u d hΓ]
    exact hW.inner tendsto_const_nhds
  apply ge_of_tendsto (x := atTop) (f := fun k : ℕ => bochnerTestForm μ Q (-K) G (W k)-
    weightedGamma μ Q (SobolevSpace.toLp μ Q (W k)) u d) ?_ (Eventually.of_forall hpos)
  simpa only [bochnerTestForm_apply,Function.comp_apply] using!
    ((hE.const_mul (-(1/2:ℝ))).add (hI.const_mul (-K))).sub hJ

end RegularPointCoordinates

end

end OAI
