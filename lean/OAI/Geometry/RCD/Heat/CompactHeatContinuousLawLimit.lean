import OAI.Geometry.RCD.Heat.CompactHeatLawLimits
import OAI.Geometry.RCD.Heat.CompactHeatTestTimeBound
import OAI.Geometry.RCD.Sobolev.FiniteDominatedCurveLimit

namespace OAI

/-! # One continuous limit curve for the actual compact heat laws

All interior times share the same noise subsequence. The probability curve
is constructed from the actual heat densities and retains the same uniform
density bound; every ambient L1 function can be tested at every time.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem interpolationLaw_continuous_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ y:S, dist z y ≤ R) (hT : ∀ y:T, dist z y ≤ R) (i : ℕ → ℕ) :
    ∃ (C : ℝ) (Q : Ioo (0:ℝ) 1 → ProbabilityMeasure X) (j : ℕ → ℕ),
      0 < C ∧ StrictMono j ∧ Continuous Q ∧ ∀ t,
      Tendsto (fun k => D.interpolationLaw (i (j k)) t) atTop (𝓝 (Q t)) ∧
      (Q t : Measure X) ≤ ENNReal.ofReal C • hausdorff n X ∧
      ∀ f : X → ℝ, Integrable f (hausdorff n X) →
        Tendsto (fun k => ∫ x, D.interpolationDensity (i (j k)) t x*f x ∂hausdorff n X)
          atTop (𝓝 (∫ x, f x ∂(Q t : Measure X))) := by
  let m := hausdorff n X
  let : Nonempty (Ioo (0:ℝ) 1) := ⟨⟨1/2,by norm_num⟩⟩
  let s := denseSeq (Ioo (0:ℝ) 1)
  obtain ⟨σ,hσ⟩ := D.interpolationLaw_finite_dominator hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν z hR hS hT
  obtain ⟨Qd,j,hj,hjd⟩ := countable_probability_subsequence_of_finite_dominator σ
    (fun l k => D.interpolationLaw (i k) (s l)) (fun l k => hσ (i k) (s l))
  have hlocal (g : X →ᵇ ℝ) (L : ℝ≥0) (hg : LipschitzWith L g) (hgc : HasCompactSupport g)
      (t : Ioo (0:ℝ) 1) : ∃ (A : ℝ≥0) (r : ℝ), 0 < r ∧ ∀ k,
        LipschitzOnWith A (fun t => ∫ x, g x ∂(D.interpolationLaw (i (j k)) t : Measure X)) (Metric.ball t r) := by
    let δ := min (t:ℝ) (1-t)/2
    have hδ : 0 < δ := half_pos (lt_min t.property.1 (sub_pos.mpr t.property.2))
    have ht : (t:ℝ) ∈ Ioo δ (1-δ) := by
      have hδ' := hδ
      dsimp only [δ] at hδ'
      dsimp only [δ]
      constructor <;> linarith [min_le_left (t:ℝ) (1-t),min_le_right (t:ℝ) (1-t)]
    have hopen : IsOpen {v : Ioo (0:ℝ) 1 | (v:ℝ) ∈ Ioo δ (1-δ)} :=
      isOpen_Ioo.preimage continuous_subtype_val
    obtain ⟨r,hr,hrsub⟩ := Metric.isOpen_iff.mp hopen t ht
    obtain ⟨A,hA⟩ := D.interpolationLaw_test_lipschitz hε1
      ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν z (le_trans (by norm_num) hR) hS hT hδ g hg hgc
    refine ⟨A,r,hr,fun k => (hA (i (j k))).mono ?_⟩
    intro v hv
    exact ⟨(hrsub hv).1.le,(hrsub hv).2.le⟩
  obtain ⟨Q,hQc,hlimit⟩ := finite_dominated_curve_limit σ
    (fun k t => D.interpolationLaw (i (j k)) t) s (denseRange_denseSeq _) (fun k t => hσ _ t)
    hlocal (fun l => ⟨Qd l,hjd l⟩)
  have hlim t := (hlimit t).1
  obtain ⟨C,hC,hbound⟩ := D.interpolationDensity_uniform_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν z hR hS hT
  have hdom (t : Ioo (0:ℝ) 1) (k : ℕ) :
      (D.interpolationLaw (i (j k)) t : Measure X) ≤ ENNReal.ofReal C • m := by
    rw [← withDensity_const]
    apply withDensity_mono
    exact Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hbound _ _ x)
  refine ⟨C,Q,j,hC,hj,hQc,fun t => ⟨hlim t,?_,?_⟩⟩
  · exact weak_probability_domination m _ (Q t) (hlim t) ENNReal.ofReal_ne_top (hdom t)
  · intro f hf
    have he := weak_probability_integral_L1 m _ (Q t) (hlim t) ENNReal.ofReal_ne_top (hdom t) hf
    simpa only [D.interpolationLaw_integral] using he

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
