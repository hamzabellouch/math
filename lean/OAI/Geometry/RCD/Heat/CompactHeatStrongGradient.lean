import OAI.Geometry.RCD.Metric.FixedGaugeLocalSourceMass
import OAI.Geometry.RCD.Sobolev.RadialSourceStrongGradient
import OAI.Geometry.RCD.Metric.FixedGaugeLocalBounds

namespace OAI

/-! # Strong local gradients of the actual fixed-gauge heat potentials

Uniform convergence of values now implies convergence of local gradient
differences. The local L1 source bound is constructed from the RCD heat
estimates, rather than supplied as a compactness premise.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_strong_gradient (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S,ℝ)) (hF : ∀ k y, 0 < F k y)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (z : X) {R r δ t : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hdist : ∀ y:S, dist z y ≤ R) (hδ : 0 < δ) (ht : t ∈ Icc δ 1)
    (f : X → ℝ)
    (hc : TendstoUniformly (fun k (x : closedBall z (2*r)) =>
      hX.fixedGaugeScaledPotential hn p ν (F k) (ε k) (hε k) δ hδ z t x)
      (fun x => f x) atTop)
    (φ : X → ℝ) {Lφ Bφ : ℝ≥0} (hφ : LipschitzWith Lφ φ)
    (hs : HasCompactSupport φ) (hBφ : ∀ x, |φ x| ≤ Bφ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hzero : ∀ x ∉ closedBall z r, φ x = 0) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    ∃ (w : ℕ → SobolevSpace μ Q) (v : SobolevSpace μ Q),
      (∀ k, SobolevSpace.toLp μ Q (w k) =ᵐ[μ] fun x => radialCutoff z r x*
        hX.fixedGaugeScaledPotential hn p ν (F k) (ε k) (hε k) δ hδ z t x) ∧
      (SobolevSpace.toLp μ Q v =ᵐ[μ] fun x => radialCutoff z r x*f x) ∧
      (∀ ℓ : SobolevSpace μ Q →L[ℝ] ℝ, Tendsto (fun k => ℓ (w k)) atTop (𝓝 (ℓ v))) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ k, ∀ᵐ x ∂μ, localGamma μ Q (w k-v) (w k-v) x ≤ C) ∧
      Tendsto (fun k => weightedGamma μ Q (fun x => (φ x)^2) (w k-v) (w k-v)) atTop (𝓝 0) := by
  intro μ Q
  let g := fun k => hX.fixedGaugeScaledPotential hn p ν (F k) (ε k) (hε k) δ hδ z t
  obtain ⟨L,A,hbound⟩ := hX.fixed_gauge_local_bounds hn p hK ν ρ hρ hρ0 hB hν
    z hR hdist (r := 2*r) (by positivity) hδ
  have hgl (k : ℕ) : LipschitzOnWith L (g k) (closedBall z (2*r)) :=
    (hbound (F k) (hF k) (ε k) (hε k) (hε1 k) t ht).1
  have hgb (k : ℕ) : ∀ x ∈ closedBall z (2*r), |g k x| ≤ A :=
    (hbound (F k) (hF k) (ε k) (hε k) (hε1 k) t ht).2
  have hp (x : X) (hx : x ∈ closedBall z (2*r)) :
      Tendsto (fun k => g k x) atTop (𝓝 (f x)) := hc.tendsto_at ⟨x,hx⟩
  have hfl : LipschitzOnWith L f (closedBall z (2*r)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto ((hp x hx).dist (hp y hy))
      (Eventually.of_forall fun k => (hgl k).dist_le_mul x hx y hy)
  have hfb : ∀ x ∈ closedBall z (2*r), |f x| ≤ A := by
    intro x hx
    exact le_of_tendsto (hp x hx).abs (Eventually.of_forall fun k => hgb k x hx)
  let η := SobolevSpace.ofLipschitzCompact μ Q hφ hs
  have hη : SobolevSpace.toLp μ Q η =ᵐ[μ] φ := SobolevSpace.ofLipschitzCompact_coe μ Q hφ hs
  have hgrad := SobolevSpace.minimalSlope_le_lipschitz μ Q η hφ hη
  obtain ⟨_Ls,C,hC,hsource⟩ := hX.fixed_gauge_local_source_mass hn p hK ν ρ hρ hρ0 hB hν
    z hR hr hdist hδ η φ hη (hφ.continuous.integrable_of_hasCompactSupport hs) hφ0 hzero Lφ hgrad
  let w := fun k => radialLocalSobolev μ Q z hr (hgl k) (hgb k)
  let v := radialLocalSobolev μ Q z hr hfl hfb
  let E : ℝ≥0 := A*⟨r⁻¹,inv_nonneg.mpr hr.le⟩+L
  have hwbound (k : ℕ) : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q (w k) x ≤ E :=
    SobolevSpace.minimalSlope_le_lipschitz μ Q (w k)
      (radial_local_lipschitz_cutoff z hr (hgl k) (hgb k)).1
      (radialLocalSobolev_coe μ Q z hr (hgl k) (hgb k))
  have hvbound : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q v x ≤ E :=
    SobolevSpace.minimalSlope_le_lipschitz μ Q v
      (radial_local_lipschitz_cutoff z hr hfl hfb).1 (radialLocalSobolev_coe μ Q z hr hfl hfb)
  have hcap : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ∀ᵐ x ∂μ, localGamma μ Q (w k-v) (w k-v) x ≤ C := by
    refine ⟨(2*(E:ℝ))^2,sq_nonneg _,fun k => ?_⟩
    filter_upwards [hwbound k,hvbound,
      (Lp.coeFn_le _ _).mpr (SobolevSpace.minimalSlope_sub_le μ Q (w k) v),
      Lp.coeFn_add (SobolevSpace.minimalSlope μ Q (w k)) (SobolevSpace.minimalSlope μ Q v),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q (w k-v)),
      localGamma_self μ Q (w k-v)] with x hw hv hsub hadd hn he
    rw [he]
    rw [hadd] at hsub
    change SobolevSpace.minimalSlope μ Q (w k-v) x ≤
      SobolevSpace.minimalSlope μ Q (w k) x+SobolevSpace.minimalSlope μ Q v x at hsub
    exact (sq_le_sq₀ hn (by positivity)).mpr (by linarith)
  refine ⟨w,v,fun k => radialLocalSobolev_coe μ Q z hr (hgl k) (hgb k),
    radialLocalSobolev_coe μ Q z hr hfl hfb,
    radialLocalSobolev_weak_limit μ Q z hr g f L A hgl hfl hgb hfb hp,hcap,?_⟩
  apply radial_source_strong_gradient μ Q z hr g f L A hgl hfl hgb hfb hc
    φ hφ hs hBφ hφ0 hzero hC
  intro k
  obtain ⟨u,d,hd,hu,_hL,hi,hm⟩ := hsource (F k) (hF k) (hε k) (hε1 k) ht.1 ht.2
  exact ⟨u,d,hd,hu,hi,hm⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
