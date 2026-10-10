import OAI.Geometry.RCD.Heat.CompactHeatHarmonicSecondVariation
import OAI.Geometry.RCD.Heat.HeatMeanStrongLimit
import OAI.Geometry.RCD.Harmonic.VanishingVariationAffineLimit

namespace OAI

/-! # Affine means for original harmonic constant-energy coordinates -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {n : ℕ} {hX : NoncollapsedRCD 0 n X} {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem affine_original_harmonic_mean (a₀ : S) (b₀ : T)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (j : ℕ → ℕ) (hj : StrictMono j) (Q₀ : Ioo (0:ℝ) 1 → ProbabilityMeasure X)
    (hweak : ∀ t, Tendsto (fun k => D.interpolationLaw (D.index (j k)) t) atTop (𝓝 (Q₀ t)))
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (U : X → ℝ) (L A : ℝ≥0) (hU : LipschitzWith L U) (hUc : HasCompactSupport U)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] U)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x| ≤ A)
    {b : ℝ} (hb : 24*R < b)
    (hd0 : d =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => 0) (c : ℝ)
    (hc : localGamma (hausdorff n X) hX.quadratic u u
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c) :
    ∃ α β : ℝ, ∀ t : Ioo (0:ℝ) 1,
      (∫ x, U x ∂(Q₀ t : Measure X)) = α*(t:ℝ)+β := by
  let m := hausdorff n X
  let q := hX.quadratic
  let f := SobolevSpace.toLp m q u
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let H k := kernelHeat m q hk (heatStep k) f
  let F k t := if ht : t ∈ Ioo (0:ℝ) 1 then ∫ x, H k x ∂(Q₀ ⟨t,ht⟩ : Measure X) else 0
  let Z t := if ht : t ∈ Ioo (0:ℝ) 1 then ∫ x, U x ∂(Q₀ ⟨t,ht⟩ : Measure X) else 0
  obtain ⟨G,hF,hint,hG⟩ := D.harmonic_heat_second_variation a₀ b₀ hε1 hε0
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT j hj Q₀ hweak
    u d hd U L A hU hUc hu hA hb hd0 c hc heatStep heatStep_pos heatStep_tendsto
  obtain ⟨B,_hB,hden⟩ := D.interpolationDensity_uniform_bound le_rfl hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν p hR hS hT
  have hQ (t : Ioo (0:ℝ) 1) : (Q₀ t : Measure X) ≤ ENNReal.ofReal B • m := by
    apply weak_probability_domination m _ _ (hweak t) ENNReal.ofReal_ne_top
    intro k
    rw [← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hden _ _ x))
  have hmeans := heat_means_uniform_limit m q hk (fun t => (Q₀ t : Measure X))
    ENNReal.ofReal_ne_top hQ f U hu heatStep heatStep_pos heatStep_tendsto
  obtain ⟨α,β,hab⟩ := affine_of_vanishing_second_variation F G Z hF
    (fun k a b ha hab hb => (hint k a b ha hab hb).2) hG (fun t ht => by
      simpa only [F,Z,dite_eq_left ht] using hmeans.tendsto_at ⟨t,ht⟩)
  exact ⟨α,β,fun t => by simpa only [Z,dite_eq_left t.property] using hab t t.property⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
