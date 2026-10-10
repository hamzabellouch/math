import OAI.Geometry.RCD.Sobolev.CanonicalHessianRestriction
import OAI.Geometry.RCD.Sobolev.CanonicalHessianLocality

namespace OAI

/-! # The same intrinsic Hessian pairing on a smaller supported law -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)
  [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem canonical_hessian_inner_pairing (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {s r R : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hrR : r ≤ R)
    (v z : SobolevSpace (hausdorff n X) hX.quadratic)
    (V Z : X → ℝ) (Lv Lz Av Az : ℝ≥0)
    (hV : LipschitzWith Lv V) (hZ : LipschitzWith Lz Z)
    (hVc : HasCompactSupport V) (hZc : HasCompactSupport Z)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X] V)
    (hz : SobolevSpace.toLp (hausdorff n X) hX.quadratic z =ᵐ[hausdorff n X] Z)
    (hAv : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic v x| ≤ Av)
    (hAz : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic z x| ≤ Az)
    (hvz : SobolevSpace.toLp (hausdorff n X) hX.quadratic v
      =ᵐ[(hausdorff n X).restrict (closedBall p r)]
        SobolevSpace.toLp (hausdorff n X) hX.quadratic z)
    (ψ φ : X → ℝ) (hψ : AEStronglyMeasurable ψ (hausdorff n X))
    (hφ : AEStronglyMeasurable φ (hausdorff n X)) (B D : ℝ≥0)
    (hB : ∀ᵐ x ∂hausdorff n X, |ψ x| ≤ B)
    (hD : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ D)
    (hψone : ∀ x∈closedBall p r, ψ x=1) (hφz : ∀ x∉closedBall p r, φ x=0)
    (J : Lp ℝ 1 ((hausdorff n X).restrict (closedBall p R)))
    (I : Lp ℝ 1 ((hausdorff n X).restrict (closedBall p r)))
    (hJ : IsCanonicalHeatHessian (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic s hs f) v p R ψ J)
    (hI : IsCanonicalHeatHessian (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic s hs f) z p r φ I)
    (ν : Measure X) (hν : ν ≪ hausdorff n X)
    (hstay : ∀ᵐ x ∂ν, x∈closedBall p r) (hone : φ =ᵐ[ν] fun _ => 1) :
    (∫ x in closedBall p r, I x ∂ν) = ∫ x in closedBall p R, J x ∂ν := by
  let m := hausdorff n X
  let q := hX.quadratic
  obtain ⟨Jr,hJr,he⟩ := hJ.restrict_weight m q hrR hψ B hB hψone φ hφ D hD
  have hsame := hX.canonical_hessian_locality hn p hK f A hf hs hr
    v z V Z Lv Lz Av Az hV hZ hVc hZc hv hz hAv hAz hvz φ hφ D hD hφz Jr I hJr hI
  rw [hsame] at he
  have hsmall : ν.restrict (closedBall p r)=ν := Measure.restrict_eq_self_of_ae_mem hstay
  have hlarge : ν.restrict (closedBall p R)=ν := Measure.restrict_eq_self_of_ae_mem
    (hstay.mono fun _ hx => (closedBall_subset_closedBall hrR) hx)
  have heν := (hν.restrict (closedBall p r)).ae_eq he
  rw [hsmall] at heν
  rw [hsmall,hlarge]
  apply integral_congr_ae
  filter_upwards [heν,hone] with x hx hφx
  simpa only [hφx,one_mul] using hx

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
