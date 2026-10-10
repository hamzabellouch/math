import OAI.Geometry.RCD.Heat.CompactHeatActionRealization

namespace OAI

/-! # Common compact Lipschitz bounds for an entire interior family of heat actions -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem uniform_compact_heat_action_realization (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S,ℝ)) (hF : ∀ k y, 0 < F k y)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (z : X) (ι : ℕ → ℕ) (H : ℝ → X → ℝ)
    (hconv : hX.CompactHeatConverges hn p ν F ε hε z ι H)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ y:S, dist z y ≤ R) :
    let m := hausdorff n X
    let q := hX.quadratic
    ∃ Lv Av : ℝ≥0, ∀ t ∈ Ioo δ 1,
      ∃ (v : SobolevSpace m q) (V : X → ℝ),
        LipschitzWith Lv V ∧ HasCompactSupport V ∧
        (SobolevSpace.toLp m q v =ᵐ[m] V) ∧
        (∀ᵐ x ∂m, |SobolevSpace.toLp m q v x| ≤ Av) ∧
        (SobolevSpace.toLp m q v =ᵐ[m.restrict (closedBall z r)] H t) := by
  intro m q
  obtain ⟨L,A,hbound⟩ := hX.fixed_gauge_local_bounds hn p hK ν ρ hρ hρ0 hB hν
    z hR hdist (r := 2*r) (by positivity) hδ
  refine ⟨A*⟨r⁻¹,inv_nonneg.mpr hr.le⟩+L,A,?_⟩
  intro t ht
  let g (k : ℕ) := hX.fixedGaugeScaledPotential hn p ν (F (ι k))
    (ε (ι k)) (hε (ι k)) δ hδ z t
  have hgl (k : ℕ) : LipschitzOnWith L (g k) (closedBall z (2*r)) :=
    (hbound (F (ι k)) (hF (ι k)) (ε (ι k)) (hε (ι k)) (hε1 (ι k)) t
      ⟨ht.1.le,ht.2.le⟩).1
  have hgb (k : ℕ) : ∀ x ∈ closedBall z (2*r), |g k x| ≤ A :=
    (hbound (F (ι k)) (hF (ι k)) (ε (ι k)) (hε (ι k)) (hε1 (ι k)) t
      ⟨ht.1.le,ht.2.le⟩).2
  have hp (x : X) (hx : x ∈ closedBall z (2*r)) :
      Tendsto (fun k => g k x) atTop (𝓝 (H t x)) :=
    (hconv (2*r) (by positivity) δ hδ t ht).tendsto_at ⟨x,hx⟩
  have hfl : LipschitzOnWith L (H t) (closedBall z (2*r)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto ((hp x hx).dist (hp y hy))
      (Eventually.of_forall fun k => (hgl k).dist_le_mul x hx y hy)
  have hfb : ∀ x ∈ closedBall z (2*r), |H t x| ≤ A := by
    intro x hx
    exact le_of_tendsto (hp x hx).abs (Eventually.of_forall fun k => hgb k x hx)
  let v := radialLocalSobolev m q z hr hfl hfb
  let V := fun x => radialCutoff z r x*H t x
  have hv : SobolevSpace.toLp m q v =ᵐ[m] V := radialLocalSobolev_coe m q z hr hfl hfb
  refine ⟨v,V,(radial_local_lipschitz_cutoff z hr hfl hfb).1,
    (radialCutoff_hasCompactSupport z hr).mul_right,hv,?_,
    radialLocalSobolev_eq_on_ball m q z hr hfl hfb⟩
  filter_upwards [hv] with x hx
  rw [hx]
  exact (radial_local_lipschitz_cutoff z hr hfl hfb).2 x

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
