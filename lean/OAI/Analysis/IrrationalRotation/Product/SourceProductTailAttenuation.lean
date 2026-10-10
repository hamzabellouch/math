import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences
import OAI.Analysis.IrrationalRotation.Product.ProductScaleTailAttenuation
import OAI.Analysis.IrrationalRotation.Couplings.SourceCouplingMarginals
import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalEvents
import OAI.Analysis.IrrationalRotation.Product.ProductCircleConditioning

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Invariant233.ProductScaleLaws
open OrderedProductCoupling

variable {p : ProductScaleData} (hp : ProductScaleLaws p)

theorem source_product_tail_conditional_attenuation
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (j : ℕ)
    (hb : ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Icc (1 / p.N j) (2 / p.N j))
    (hsmall : ∀ s, j < s → ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ s, j ≤ s → ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ) :
    let P := sourceBlocks p.m p.a p.b hp.m_ge_100
      (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
      (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j
    ∃ H₁ H₂ : ℤ → Set Sample,
      (∀ k, MeasurableSet (H₁ k)) ∧ (∀ k, MeasurableSet (H₂ k)) ∧
      (∀ᵐ ω ∂law P, ∀ k : ℤ, (p.K j : ℝ) < |(k : ℝ)| →
        ((law P)[(H₁ k).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap circleLeftEndpoint inferInstance]) ω ≤
            Real.exp (-p.L j / 400) ∧
        ((law P)[(H₂ k).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap circleRightEndpoint inferInstance]) ω ≤
            Real.exp (-p.L j / 400) ∧
        ((∃ i ∈ ProductPhases.consecutiveBlock p.m j,
          circleRepresentative (circleLeftEndpoint ω i) < 1 / (p.m j : ℝ) ∧
          1 - 1 / (p.m j : ℝ) ≤ circleRepresentative (circleRightEndpoint ω i)) →
          ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (circleRightEndpoint ω) /
            ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (circleLeftEndpoint ω) ≤
            Real.exp (-p.L j) + (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
              (H₂ k).indicator (fun _ => (1 : ℝ)) ω)) := by
  let P := sourceBlocks p.m p.a p.b hp.m_ge_100
    (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
    (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j
  change ∃ H₁ H₂ : ℤ → Set Sample, _
  let u : ℤ → ℕ → ℝ := fun k i => 1 - Int.fract ((k : ℝ) * θ i)
  let top : ℤ → Bool → ℕ → Set Sample := fun k _ i =>
    {ω | u k i ≤ realEndpoint (circleRightEndpoint ω) i}
  let bottom : ℤ → Bool → ℕ → Set Sample := fun k _ i =>
    {ω | realEndpoint (circleLeftEndpoint ω) i < u k i}
  have htop (k : ℤ) (which : Bool) (i : ℕ) : MeasurableSet (top k which i) :=
    measurableSet_le measurable_const
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp circleRightEndpoint_measurable))
  have hbottom (k : ℤ) (which : Bool) (i : ℕ) : MeasurableSet (bottom k which i) :=
    measurableSet_lt
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp circleLeftEndpoint_measurable))
      measurable_const
  have hac (side : Bool) : (law P).map (circleHybridEndpoint (fun _ => side)) ≪
      ProductCocycle.haar ℕ := by
    obtain ⟨g, _, _, _, _, hg⟩ := exists_source_circle_hybrid_density p.m p.a p.b
      hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
      (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j (fun _ => side)
    change (law P).map (circleHybridEndpoint (fun _ => side)) = _ at hg
    rw [hg]
    exact withDensity_absolutelyContinuous _ _
  have hacx : (law P).map circleLeftEndpoint ≪ ProductCocycle.haar ℕ := hac false
  have hacy : (law P).map circleRightEndpoint ≪ ProductCocycle.haar ℕ := hac true
  apply hp.simultaneous_product_tail_conditional_attenuation e he θ hθ0 hθsum
    (MeasurableSpace.comap circleLeftEndpoint inferInstance)
    (MeasurableSpace.comap circleRightEndpoint inferInstance)
    circleLeftEndpoint_measurable.comap_le circleRightEndpoint_measurable.comap_le
    (law P) circleLeftEndpoint circleRightEndpoint
    (Measurable.of_comap_le le_rfl) (Measurable.of_comap_le le_rfl)
    hacx hacy (ae_circle_endpoints_ordered P) top bottom htop hbottom
    (fun k _ => (right_threshold_iCondIndepSet_iff_circle P (u k)).mp
      (right_thresholds_iCondIndepSet P (u k)))
    (fun k _ => (left_threshold_iCondIndepSet_iff_circle P (u k)).mp
      (left_thresholds_iCondIndepSet P (u k)))
    j hb hsmall hlarge
  · intro k s _hjs which i hi _u hu
    have hsi := ProductPhases.enumeration_block_of_mem p.m e he hi
    let w : ℝ := if which then p.b s else p.a s
    have hw : w = P.a i ∨ w = P.b i := by
      cases which
      · exact Or.inl (by simp only [w, P, sourceBlocks, ofBlocks, hsi, Bool.false_eq_true, ↓reduceIte])
      · exact Or.inr (by simp only [w, P, sourceBlocks, ofBlocks, hsi, ↓reduceIte])
    have hrho : CouplingMarginalBounds.rho (P.κ i) (P.m i) w =
        ProductScaleData.kappa s * Real.sqrt (w / (p.m s : ℝ)) := by
      simp only [CouplingMarginalBounds.rho, P, sourceBlocks, ofBlocks, hsi,
        sourceKappa, ProductScaleData.kappa, Nat.cast_add, Nat.cast_one]
    filter_upwards [ae_real_circle_endpoints P,
      right_threshold_condExp_lower P (u k), left_threshold_condExp_lower P (u k),
      right_threshold_condExp_eq_circle P (u k) i,
      left_threshold_condExp_eq_circle P (u k) i]
      with ω hrep hr hl her hel
    refine ⟨fun _ h => h, fun _ h => h, ?_, ?_⟩
    · intro hx
      have hxr : leftEndpoint ω i < u k i := by
        rw [← hrep.1]
        exact hx
      have h := hr i w hw hu.1 hu.2 hxr
      rw [hrho, her] at h
      exact h
    · intro hy
      have hyr : u k i ≤ rightEndpoint ω i := by
        rw [← hrep.2]
        exact hy
      have h := hl i w hw hu.1 hu.2 hyr
      rw [hrho, hel] at h
      exact h
  · exact Filter.Eventually.of_forall (fun _ h => h)

end Invariant233.ProductScaleLaws

end

end OAI
