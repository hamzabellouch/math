import OAI.Analysis.Brenier.MapDistance
import OAI.Analysis.Brenier.Wasserstein

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ} {ρ : Measure (E d)} {T S : E d → E d}

/-- The common-source plan bounds transport distance by map distance. -/
theorem wasserstein2_map_le_mapL2Dist [IsProbabilityMeasure ρ]
    (hT : Measurable T) (hS : Measurable S)
    (hInt : Integrable (fun x => ‖T x - S x‖ ^ 2) ρ) :
    wasserstein2 (Measure.map T ρ) (Measure.map S ρ) ≤ mapL2Dist ρ T S := by
  have hPair : Measurable (fun x => (T x, S x)) := hT.prodMk hS
  have hπ : IsCoupling (Measure.map T ρ) (Measure.map S ρ)
      (Measure.map (fun x => (T x, S x)) ρ) := by
    refine ⟨inferInstance, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hPair]
      rfl
    · rw [Measure.map_map measurable_snd hPair]
      rfl
  rw [mapL2Dist_eq_sqrt_pair_cost hT hS]
  apply wasserstein2_le_of_coupling hπ
  rw [quadraticPlanCost_map_pair hT hS,
    ← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun x => sq_nonneg _)]
  exact ENNReal.ofReal_ne_top

/-- The same inequality for maps presented with specified pushforward laws. -/
theorem wasserstein2_le_mapL2Dist [IsProbabilityMeasure ρ]
    {μ ν : Measure (E d)} (hT : Measurable T) (hS : Measurable S)
    (hμ : Measure.map T ρ = μ) (hν : Measure.map S ρ = ν)
    (hInt : Integrable (fun x => ‖T x - S x‖ ^ 2) ρ) :
    wasserstein2 μ ν ≤ mapL2Dist ρ T S := by
  rw [← hμ, ← hν]
  exact wasserstein2_map_le_mapL2Dist hT hS hInt

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem358

variable {d : ℕ} {ρ μ ν : Measure (E d)} [IsProbabilityMeasure ρ]

/-- Bounds from coupling-dependent optimal maps transfer to a single pair of maps
before taking the cost infimum. Plan uniqueness makes the choice harmless. -/
theorem exists_optimal_maps_wasserstein_bound_of_coupling_bounds
    {π₀ : Measure (E d × E d)} (hπ₀ : IsCoupling μ ν π₀)
    (hfinite : quadraticPlanCost π₀ ≠ ∞) {C α : ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hbound : ∀ π : Measure (E d × E d), IsCoupling μ ν π →
      quadraticPlanCost π ≠ ∞ →
      ∃ T S : E d → E d, IsUniqueQuadraticOptimalMap ρ μ T ∧
        IsUniqueQuadraticOptimalMap ρ ν S ∧
        mapL2Dist ρ T S ≤ C * Real.rpow (Real.sqrt (quadraticPlanCost π).toReal) α) :
    ∃ T S : E d → E d, IsUniqueQuadraticOptimalMap ρ μ T ∧
      IsUniqueQuadraticOptimalMap ρ ν S ∧
      mapL2Dist ρ T S ≤ C * Real.rpow (wasserstein2 μ ν) α := by
  obtain ⟨T, S, hT, hS, _⟩ := hbound π₀ hπ₀ hfinite
  refine ⟨T, S, hT, hS, ?_⟩
  apply le_mul_rpow_wasserstein2_of_coupling_bound hπ₀ hfinite hC hα
  intro π hπ hfin
  obtain ⟨T', S', hT', hS', hb⟩ := hbound π hπ hfin
  rw [mapL2Dist_eq_of_optimal_maps hT hS hT'.1 hS'.1]
  exact hb

/-- Approximate estimates may also choose different unique optimal maps for every
positive error. The limiting estimate needs neither a compactness argument nor
convergence of these representatives. -/
theorem exists_optimal_maps_bound_of_approximate_bounds
    {F : ℝ → ℝ} {w : ℝ} (hcont : ContinuousAt F w)
    (hbound : ∀ ε : ℝ, 0 < ε →
      ∃ T S : E d → E d, IsUniqueQuadraticOptimalMap ρ μ T ∧
        IsUniqueQuadraticOptimalMap ρ ν S ∧ mapL2Dist ρ T S ≤ F (w + ε)) :
    ∃ T S : E d → E d, IsUniqueQuadraticOptimalMap ρ μ T ∧
      IsUniqueQuadraticOptimalMap ρ ν S ∧ mapL2Dist ρ T S ≤ F w := by
  obtain ⟨T, S, hT, hS, _⟩ := hbound 1 zero_lt_one
  refine ⟨T, S, hT, hS, ?_⟩
  have hlim : Tendsto (fun ε : ℝ => F (w + ε)) (𝓝[>] 0) (𝓝 (F w)) := by
    apply hcont.tendsto.comp
    simpa using (tendsto_const_nhds.add
      (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun ε : ℝ => w + ε) (𝓝[>] 0) (𝓝 (w + 0)))
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨T', S', hT', hS', hb⟩ := hbound ε hε
  rw [mapL2Dist_eq_of_optimal_maps hT hS hT'.1 hS'.1]
  exact hb

end Problem358

end

end OAI
