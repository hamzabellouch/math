import OAI.Geometry.RCD.Heat.CompactHeatOsmoticRate

namespace OAI

/-! # Uniform disappearance of the actual local osmotic energy -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates

def InteriorHeatTime (δ : ℝ) :=
  {t : Ioo (0:ℝ) 1 // δ ≤ (t:ℝ) ∧ δ ≤ 1-(t:ℝ)}

namespace NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

def osmoticPotential (k : ℕ) (t : Ioo (0:ℝ) 1) (x : X) : ℝ :=
  (ε k/4)*Real.log (D.interpolationDensity k t x)

theorem local_osmotic_vanishes (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R r δ : ℝ} (hR : 0 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ a : T, dist z a ≤ R) (hδ : 0 < δ)
    (φ : X → ℝ) (M : ℝ≥0) (hφ : LipschitzWith M φ) (hφs : HasCompactSupport φ)
    (hφ01 : ∀ x, φ x ∈ Icc (0:ℝ) 1) (hsupp : tsupport φ ⊆ closedBall z r) :
    ∃ η : ℕ → InteriorHeatTime δ → SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (η k t)
        =ᵐ[(hausdorff n X).restrict (tsupport φ)] D.osmoticPotential k t.val) ∧
      TendstoUniformly (fun k t => weightedGamma (hausdorff n X) hX.quadratic
        (fun x => φ x*D.interpolationDensity k t.val x) (η k t) (η k t)) (fun _ => 0) atTop := by
  classical
  obtain ⟨C,hC,hdata⟩ := D.local_osmotic_rate hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁
    hμ hν z hR hS hT hδ φ M hφ hφs hφ01 hsupp
  choose η hη hb using fun k (t : InteriorHeatTime δ) => hdata k t.val t.property.1 t.property.2
  refine ⟨η,?_,?_⟩
  · intro k t
    filter_upwards [hη k t] with x hx
    rw [hx]
    dsimp only [osmoticPotential,interpolationDensity]
    rw [Real.log_mul
      (hX.compactHeatFactor_positive hn p μ (D.left k) (D.left_pos k) _ _ x).ne'
      (hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k) _ _ x).ne']
  · apply Metric.tendstoUniformly_iff.mpr
    intro e he
    have htend : Tendsto (fun k => (ε k/4)*C) atTop (𝓝 0) := by
      simpa only [zero_div,zero_mul] using (hε0.div_const 4).mul_const C
    filter_upwards [htend.eventually (gt_mem_nhds he)] with k hk t
    have hnonneg : 0 ≤ weightedGamma (hausdorff n X) hX.quadratic
        (fun x => φ x*D.interpolationDensity k t.val x) (η k t) (η k t) := by
      apply integral_nonneg_of_ae
      filter_upwards [localGamma_self (hausdorff n X) hX.quadratic (η k t)] with x hx
      rw [hx]
      exact mul_nonneg (mul_nonneg (hφ01 x).1 (D.interpolationDensity_pos k t.val x).le) (sq_nonneg _)
    simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg hnonneg] using (hb k t).trans_lt hk

end NoncollapsedRCD.CompactHeatScalingData
end RegularPointCoordinates

end

end OAI
