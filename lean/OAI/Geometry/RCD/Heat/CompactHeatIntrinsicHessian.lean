import OAI.Geometry.RCD.Heat.CompactHeatHessianL1Limit
import OAI.Geometry.RCD.Sobolev.CanonicalHessianApproximation

namespace OAI

/-! # The actual forward action determines its canonical local Hessian limit -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_intrinsic_hessian_limit (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S,ℝ)) (hF : ∀ k y, 0 < F k y)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (z : X) (ι : ℕ → ℕ) (H : ℝ → X → ℝ)
    (hconv : hX.CompactHeatConverges hn p ν F ε hε z ι H)
    {r δ t : ℝ} (hr : 0 < r) (hδ : 0 < δ) (ht : t ∈ Ioo δ 1)
    {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ y:S, dist z y ≤ R)
    (φ : X → ℝ) {Lφ Bφ : ℝ≥0} (hφ : LipschitzWith Lφ φ)
    (hs : HasCompactSupport φ) (hBφ : ∀ x, |φ x| ≤ Bφ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hzero : ∀ x ∉ closedBall z r, φ x = 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (v : SobolevSpace (hausdorff n X) hX.quadratic)
    (V : X → ℝ) (Lv Av : ℝ≥0) (hV : LipschitzWith Lv V) (hc : HasCompactSupport V)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X] V)
    (hAv : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic v x| ≤ Av)
    (hvloc : SobolevSpace.toLp (hausdorff n X) hX.quadratic v
      =ᵐ[(hausdorff n X).restrict (closedBall z r)] H t) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ (u WU UU : ℕ → SobolevSpace m q) (J : Lp ℝ 1 (m.restrict (closedBall z r))),
      (∀ k, SobolevSpace.toLp m q (u k) =ᵐ[m.restrict (closedBall z r)]
        hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t) ∧
      (∀ k, SobolevSpace.toLp m q (WU k) =ᵐ[m.restrict (closedBall z r)] localGamma m q w (u k)) ∧
      (∀ k, SobolevSpace.toLp m q (UU k) =ᵐ[m.restrict (closedBall z r)] localGamma m q (u k) (u k)) ∧
      IsCanonicalHeatHessian m q w v z r φ J ∧
      Tendsto (fun k => ∫ x in closedBall z r,
        |φ x*localHessianAction m q w (u k) (u k) (WU k) (WU k) (UU k) x-J x| ∂m)
        atTop (𝓝 0) := by
  intro m q w
  choose u d U L C hd hU hC hu huloc using fun k =>
    hX.fixed_gauge_heat_regular hn p ν ρ hρ hρ0 hB hν (F (ι k)) (hF (ι k))
      (hε (ι k)) hδ ht.1.le z (isCompact_closedBall z r)
  have huC (k : ℕ) : ∀ᵐ x ∂m, |SobolevSpace.toLp m q (u k) x| ≤ C k := by
    filter_upwards [hu k] with x hx
    exact hx ▸ hC k x
  obtain ⟨P,hP,hgrad⟩ := hX.fixed_gauge_gradient_bound hn p ν ρ hρ hρ0 hB hν
    z (r := r) hR hdist hδ
  have hgu (k : ℕ) : ∀ᵐ x ∂m.restrict (closedBall z r), localGamma m q (u k) (u k) x ≤ P :=
    hgrad (F (ι k)) (hF (ι k)) (ε (ι k)) (hε (ι k)) (hε1 (ι k)) t
      ⟨ht.1.le,ht.2.le⟩ (u k) (huloc k)
  obtain ⟨σ,hσ,hdata⟩ := hX.bounded_heat_mixed_hessian_density hn z hK f A hf ha hr
  choose WU WV UU hWU _hWV hUU _hH using fun k =>
    hdata (u k) (d k) (hd k) (U k) (L k) (C k) (hU k) (hu k) (huC k)
      (u k) (d k) (hd k) (U k) (L k) (C k) (hU k) (hu k) (huC k)
  have hE := hconv.strong_gradient hX hn p hK ν ρ hρ hρ0 hB hν F hF ε hε hε1
    z ι H hr hδ ht u v huloc hvloc hR hdist φ hφ hs hBφ hφ0 hzero
  obtain ⟨I,hI⟩ := hX.bounded_heat_hessian_L1_limit hn z hK f A hf ha hr u d hd U L C hU hu huC
    hP hgu φ hφ.continuous.aestronglyMeasurable Bφ (Eventually.of_forall hBφ) hzero v hE
    WU UU hWU hUU
  obtain ⟨J,hcan,_hunique⟩ := hX.exists_canonical_heat_hessian hn z hK f A hf ha hr
    v V Lv Av hV hc hv hAv φ hφ.continuous.aestronglyMeasurable Bφ (Eventually.of_forall hBφ) hzero
  have he := hX.hessian_limit_eq_canonical hn z hK f A hf ha hr u d hd U L C hU hu huC
    v V Lv Av hV hc hv hAv hP hgu φ hφ.continuous.aestronglyMeasurable Bφ
    (Eventually.of_forall hBφ) hzero hE WU UU hWU hUU I J hI hcan
  exact ⟨u,WU,UU,J,huloc,hWU,hUU,hcan,he ▸ hI⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
