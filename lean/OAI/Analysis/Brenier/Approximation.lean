import OAI.Analysis.Brenier.CompactTransport
import OAI.Analysis.Brenier.Coupling
import OAI.Analysis.Brenier.Existence

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

/-- An estimate against every finite-cost coupling descends to the transport infimum.
The finite-cost witness is essential because the definition sends infinite cost to zero. -/
theorem le_wasserstein2_add_of_le_rootCost {d : ℕ} {μ ν : Measure (E d)}
    {a δ : ℝ}
    (hfinite : ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞)
    (hbound : ∀ π : Measure (E d × E d), IsCoupling μ ν π →
      quadraticPlanCost π ≠ ∞ →
        a ≤ Real.sqrt (quadraticPlanCost π).toReal + δ) :
    a ≤ wasserstein2 μ ν + δ := by
  by_cases ha : a ≤ δ
  · linarith [wasserstein2_nonneg μ ν]
  have ht : 0 < a - δ := by linarith
  let S : Set ℝ≥0∞ := {r | ∃ π : Measure (E d × E d),
    IsCoupling μ ν π ∧ quadraticPlanCost π = r}
  have hinf : sInf S ≠ ∞ := by
    obtain ⟨π, hπ, hcost⟩ := hfinite
    exact ne_top_of_le_ne_top hcost (sInf_le ⟨π, hπ, rfl⟩)
  have hlower : ENNReal.ofReal ((a - δ) ^ 2) ≤ sInf S := by
    apply le_sInf
    rintro r ⟨π, hπ, rfl⟩
    by_cases hcost : quadraticPlanCost π = ∞
    · simp [hcost]
    apply (ENNReal.ofReal_le_iff_le_toReal hcost).2
    have hr : a - δ ≤ Real.sqrt (quadraticPlanCost π).toReal := by
      linarith [hbound π hπ hcost]
    have hs := (sq_le_sq₀ ht.le (Real.sqrt_nonneg _)).2 hr
    simpa only [Real.sq_sqrt ENNReal.toReal_nonneg] using hs
  have hs : (a - δ) ^ 2 ≤ (sInf S).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hinf).1 hlower
  have hr : a - δ ≤ wasserstein2 μ ν := Real.le_sqrt_of_sq_le hs
  linarith

/-- Quantizing the two marginals changes their Wasserstein distance by at most
 the two uniform approximation errors. This does not require an optimal coupling. -/
theorem wasserstein2_map_le {d : ℕ} {μ ν : Measure (E d)}
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hQerr : ∀ᵐ x ∂μ, ‖Q x - x‖ ≤ ε)
    (hRerr : ∀ᵐ y ∂ν, ‖R y - y‖ ≤ η)
    (hfinite : ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞) :
    wasserstein2 (Measure.map Q μ) (Measure.map R ν) ≤
      wasserstein2 μ ν + ε + η := by
  have h := le_wasserstein2_add_of_le_rootCost (δ := ε + η) hfinite
    (fun π hπ hcost =>
      (wasserstein2_le_of_coupling (hπ.map hQ hR)
        (quadraticPlanCost_map_ne_top hπ hQ hR hQerr hRerr hcost)).trans
        (by simpa only [add_assoc] using
          sqrt_quadraticPlanCost_map_le hπ hQ hR hε hη hQerr hRerr hcost))
  simpa only [add_assoc] using h

/-- Compactly supported probability marginals admit a finite-cost coupling. -/
theorem exists_finiteCost_coupling_of_compact {d : ℕ} {μ ν : Measure (E d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K Y : Set (E d)} (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    ∃ π : Measure (E d × E d), IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞ := by
  have hπ : IsCoupling μ ν (μ.prod ν) := by
    refine ⟨inferInstance, ?_, ?_⟩ <;> simp
  exact ⟨μ.prod ν, hπ, hπ.quadraticPlanCost_ne_top_of_compact hK hY hμ hν⟩

/-- The approximation inequality with the compact-support hypotheses of the challenge. -/
theorem wasserstein2_map_le_of_compact {d : ℕ} {μ ν : Measure (E d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K Y : Set (E d)} (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y)
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hQerr : ∀ᵐ x ∂μ, ‖Q x - x‖ ≤ ε)
    (hRerr : ∀ᵐ y ∂ν, ‖R y - y‖ ≤ η) :
    wasserstein2 (Measure.map Q μ) (Measure.map R ν) ≤
      wasserstein2 μ ν + ε + η :=
  wasserstein2_map_le hQ hR hε hη hQerr hRerr
    (exists_finiteCost_coupling_of_compact hK hY hμ hν)

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem358

/-- A pairwise Hölder bound in errors tending to zero is a Cauchy estimate. -/
theorem pairwise_cauchy_of_error_rpow_bound {D : ℕ → ℕ → ℝ}
    {ε : ℕ → ℝ} {C p : ℝ} (hp : 0 < p)
    (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ m n, D m n ≤ C * Real.rpow (ε m + ε n) p) :
    ∀ δ > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, D m n < δ := by
  have hsum : Tendsto (fun z : ℕ × ℕ => ε z.1 + ε z.2) atTop (𝓝 0) := by
    rw [← prod_atTop_atTop_eq]
    convert (hε.comp tendsto_fst).add (hε.comp tendsto_snd) using 1 <;>
      simp only [Function.comp_apply, zero_add]
  have hpow : Tendsto (fun z : ℕ × ℕ =>
      C * Real.rpow (ε z.1 + ε z.2) p) atTop (𝓝 0) := by
    convert (hsum.rpow_const_nhds_zero hp).const_mul C using 1
    simp only [mul_zero]
  intro δ hδ
  have hevent : ∀ᶠ z : ℕ × ℕ in atTop,
      C * Real.rpow (ε z.1 + ε z.2) p < δ := hpow.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop_prod_self'.1 hevent
  exact ⟨N, fun m hm n hn => (hbound m n).trans_lt (hN m hm n hn)⟩

/-- Finite-target one-third stability makes transport maps to a quantized target Cauchy.
The stability input here is an explicit hypothesis, not a new assumption on the challenge. -/
theorem mapL2Dist_cauchy_of_quantization_stability {d : ℕ}
    {ρ μ : Measure (E d)} [IsProbabilityMeasure μ]
    {Y : Set (E d)} (hY : IsCompact Y) (hμ : IsSupported μ Y)
    {Q T : ℕ → E d → E d} (hQ : ∀ n, Measurable (Q n))
    {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hQerr : ∀ n, ∀ᵐ x ∂μ, ‖Q n x - x‖ ≤ ε n)
    {C : ℝ} (hC : 0 ≤ C)
    (hstab : ∀ m n, mapL2Dist ρ (T m) (T n) ≤
      C * Real.rpow (wasserstein2 (Measure.map (Q m) μ) (Measure.map (Q n) μ))
        (1 / 3 : ℝ)) :
    ∀ δ > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, mapL2Dist ρ (T m) (T n) < δ := by
  apply pairwise_cauchy_of_error_rpow_bound (p := (1 / 3 : ℝ)) (C := C)
    (by norm_num) hεlim
  intro m n
  have hw : wasserstein2 (Measure.map (Q m) μ) (Measure.map (Q n) μ) ≤
      ε m + ε n := by
    simpa only [wasserstein2_self, zero_add] using
      wasserstein2_map_le_of_compact hY hY hμ hμ (hQ m) (hQ n)
        (hε m) (hε n) (hQerr m) (hQerr n)
  exact (hstab m n).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (wasserstein2_nonneg _ _) hw (by norm_num)) hC)

/-- The Cauchy estimate yields a genuine measurable L² limit of the finite maps. -/
theorem exists_limit_of_quantization_stability {d : ℕ}
    {ρ μ : Measure (E d)} [IsProbabilityMeasure μ]
    {Y : Set (E d)} (hY : IsCompact Y) (hμ : IsSupported μ Y)
    {Q T : ℕ → E d → E d} (hQ : ∀ n, Measurable (Q n))
    (hT : ∀ n, MemLp (T n) 2 ρ)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hQerr : ∀ n, ∀ᵐ x ∂μ, ‖Q n x - x‖ ≤ ε n)
    {C : ℝ} (hC : 0 ≤ C)
    (hstab : ∀ m n, mapL2Dist ρ (T m) (T n) ≤
      C * Real.rpow (wasserstein2 (Measure.map (Q m) μ) (Measure.map (Q n) μ))
        (1 / 3 : ℝ)) :
    ∃ S : E d → E d, Measurable S ∧ MemLp S 2 ρ ∧
      Tendsto (fun n => mapL2Dist ρ (T n) S) atTop (𝓝 0) :=
  exists_mapL2Dist_limit hT
    (mapL2Dist_cauchy_of_quantization_stability hY hμ hQ hε hεlim hQerr hC hstab)

/-- If all finite maps take values in the compact target almost everywhere, so does the limit. -/
theorem exists_target_limit_of_quantization_stability {d : ℕ}
    {ρ μ : Measure (E d)} [IsProbabilityMeasure μ]
    {Y : Set (E d)} (hY : IsCompact Y) (hμ : IsSupported μ Y)
    {Q T : ℕ → E d → E d} (hQ : ∀ n, Measurable (Q n))
    (hT : ∀ n, MemLp (T n) 2 ρ) (hTmem : ∀ n, ∀ᵐ x ∂ρ, T n x ∈ Y)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hQerr : ∀ n, ∀ᵐ x ∂μ, ‖Q n x - x‖ ≤ ε n)
    {C : ℝ} (hC : 0 ≤ C)
    (hstab : ∀ m n, mapL2Dist ρ (T m) (T n) ≤
      C * Real.rpow (wasserstein2 (Measure.map (Q m) μ) (Measure.map (Q n) μ))
        (1 / 3 : ℝ)) :
    ∃ S : E d → E d, Measurable S ∧ MemLp S 2 ρ ∧
      (∀ᵐ x ∂ρ, S x ∈ Y) ∧
      Tendsto (fun n => mapL2Dist ρ (T n) S) atTop (𝓝 0) :=
  exists_mapL2Dist_limit_in_closed hT
    (mapL2Dist_cauchy_of_quantization_stability hY hμ hQ hε hεlim hQerr hC hstab)
    hY.isClosed hTmem

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace Problem358

/-- Uniformly vanishing almost-everywhere quantization errors give pointwise convergence. -/
theorem ae_tendsto_of_quantization_error {d : ℕ} {μ : Measure (E d)}
    {Q : ℕ → E d → E d} {ε : ℕ → ℝ}
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hQerr : ∀ n, ∀ᵐ x ∂μ, ‖Q n x - x‖ ≤ ε n) :
    ∀ᵐ x ∂μ, Tendsto (fun n => Q n x) atTop (𝓝 x) := by
  have hall : ∀ᵐ x ∂μ, ∀ n, ‖Q n x - x‖ ≤ ε n := ae_all_iff.mpr hQerr
  filter_upwards [hall] with x hx
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun n => norm_nonneg _) hx hεlim)

/-- A strong L² limit of maps with compactly normalized supporting potentials
still has a Lipschitz supporting potential. -/
theorem exists_supporting_potential_of_mapL2_limit {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (x₀ : E d) (hx₀ : x₀ ∈ K)
    {T : ℕ → E d → E d} {S : E d → E d}
    (hT : ∀ n, MemLp (T n) 2 (uniformMeasure K))
    (hS : MemLp S 2 (uniformMeasure K))
    (hlim : Tendsto (fun n => mapL2Dist (uniformMeasure K) (T n) S) atTop (𝓝 0))
    {u : ℕ → E d → ℝ} {L : ℝ≥0}
    (hLip : ∀ n, LipschitzOnWith L (u n) K)
    (hconv : ∀ n, ConvexOn ℝ K (u n))
    (hnormal : ∀ n, u n x₀ = 0)
    (hsupport : ∀ n, ∀ᵐ x ∂uniformMeasure K,
      ∀ z ∈ K, u n x + ⟪T n x, z - x⟫ ≤ u n z) :
    ∃ v : E d → ℝ, LipschitzOnWith L v K ∧ ConvexOn ℝ K v ∧
      (∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K, v x + ⟪S x, z - x⟫ ≤ v z) := by
  obtain ⟨ns, hns, hTlim⟩ :=
    exists_subseq_tendsto_ae_of_mapL2Dist_tendsto_zero hT hS hlim
  obtain ⟨v, φ, hφ, hvlim, hvLip, hvconv, _⟩ :=
    exists_normalized_convex_potential_subseq hK x₀ hx₀ (fun n => u (ns n)) L
      (fun n => hLip (ns n)) (fun n => hconv (ns n)) (fun n => hnormal (ns n))
  have hsource : ∀ᵐ x ∂uniformMeasure K, x ∈ K :=
    Measure.ae_smul_measure (ae_restrict_mem hK.measurableSet) _
  have hTlim' : ∀ᵐ x ∂uniformMeasure K,
      Tendsto (fun n => T (ns (φ n)) x) atTop (𝓝 (S x)) := by
    filter_upwards [hTlim] with x hx
    exact hx.comp hφ.tendsto_atTop
  refine ⟨v, hvLip, hvconv, ?_⟩
  exact ae_supporting_inequality_of_pointwise_limit (uniformMeasure K) hsource
    (fun z hz => hvlim.tendsto_at hz) hTlim' (fun n => hsupport (ns (φ n)))

/-- Conditional arbitrary-target extension: finite-map stability and a fixed Lipschitz
potential bound produce a unique optimal map to the limiting target. Every finite-map
input is explicit; this theorem does not assert the missing finite stability estimate. -/
theorem exists_uniqueOptimal_limit_of_quantization {d : ℕ}
    {K Y : Set (E d)} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (x₀ : E d) (hx₀ : x₀ ∈ K)
    {μ : Measure (E d)} [IsProbabilityMeasure μ]
    (hY : IsCompact Y) (hμ : IsSupported μ Y)
    {Q T : ℕ → E d → E d} (hQ : ∀ n, Measurable (Q n))
    (hTm : ∀ n, Measurable (T n))
    (hT : ∀ n, MemLp (T n) 2 (uniformMeasure K))
    (hTmem : ∀ n, ∀ᵐ x ∂uniformMeasure K, T n x ∈ Y)
    (hpush : ∀ n, Measure.map (T n) (uniformMeasure K) = Measure.map (Q n) μ)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hQerr : ∀ n, ∀ᵐ x ∂μ, ‖Q n x - x‖ ≤ ε n)
    {C : ℝ} (hC : 0 ≤ C)
    (hstab : ∀ m n, mapL2Dist (uniformMeasure K) (T m) (T n) ≤
      C * Real.rpow (wasserstein2 (Measure.map (Q m) μ) (Measure.map (Q n) μ))
        (1 / 3 : ℝ))
    {u : ℕ → E d → ℝ} {L : ℝ≥0}
    (hLip : ∀ n, LipschitzOnWith L (u n) K)
    (hconv : ∀ n, ConvexOn ℝ K (u n))
    (hnormal : ∀ n, u n x₀ = 0)
    (hsupport : ∀ n, ∀ᵐ x ∂uniformMeasure K,
      ∀ z ∈ K, u n x + ⟪T n x, z - x⟫ ≤ u n z) :
    ∃ S : E d → E d,
      IsUniqueQuadraticOptimalMap (uniformMeasure K) μ S ∧
      MemLp S 2 (uniformMeasure K) ∧
      (∀ᵐ x ∂uniformMeasure K, S x ∈ Y) ∧
      Tendsto (fun n => mapL2Dist (uniformMeasure K) (T n) S) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (Measure.map (Q 0) μ) :=
    (Measure.isProbabilityMeasure_map_iff (hQ 0).aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (Measure.map (T 0) (uniformMeasure K)) :=
    (hpush 0).symm ▸ inferInstance
  let : IsProbabilityMeasure (uniformMeasure K) :=
    Measure.isProbabilityMeasure_of_map (hTm 0).aemeasurable
  obtain ⟨S, hSm, hS, hSmem, hlim⟩ :=
    exists_target_limit_of_quantization_stability hY hμ hQ hT hTmem
      hε hεlim hQerr hC hstab
  obtain ⟨ns, hns, hTlim⟩ :=
    exists_subseq_tendsto_ae_of_mapL2Dist_tendsto_zero hT hS hlim
  have hQlim : ∀ᵐ x ∂μ, Tendsto (fun n => Q (ns n) x) atTop (𝓝 x) := by
    filter_upwards [ae_tendsto_of_quantization_error hεlim hQerr] with x hx
    exact hx.comp hns.tendsto_atTop
  have hlaw : Measure.map S (uniformMeasure K) = μ :=
    map_eq_of_ae_limits (fun n => hTm (ns n)) hSm (fun n => hQ (ns n))
      hTlim hQlim (fun n => hpush (ns n))
  obtain ⟨v, hvLip, _, hvsupport⟩ :=
    exists_supporting_potential_of_mapL2_limit hK x₀ hx₀ hT hS hlim
      hLip hconv hnormal hsupport
  exact ⟨S, isUniqueQuadraticOptimalMap_of_supporting_potential hK hKconv
    ⟨x₀, hx₀⟩ hY hμ hvLip hSm hlaw hvsupport, hS, hSmem, hlim⟩

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal RealInnerProductSpace

namespace Problem358

/-- A paired finite-target estimate passes to arbitrary target laws. The only
quantitative assumption is the bound for the supplied approximating maps; all
limit maps and their all-plan uniqueness certificates are constructed here. -/
theorem exists_uniqueOptimal_pair_of_quantized_stability
    {d : ℕ} {K Y : Set (E d)}
    [IsFiniteMeasure (uniformMeasure K)]
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hY : IsCompact Y)
    (x₀ : E d) (hx₀ : x₀ ∈ K)
    {μ ν : Measure (E d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsSupported μ Y) (hν : IsSupported ν Y)
    (u v : ℕ → E d → ℝ) (T S Q R : ℕ → E d → E d) (L : ℝ≥0)
    (huLip : ∀ n, LipschitzOnWith L (u n) K)
    (hvLip : ∀ n, LipschitzOnWith L (v n) K)
    (huconv : ∀ n, ConvexOn ℝ K (u n))
    (hvconv : ∀ n, ConvexOn ℝ K (v n))
    (hunormal : ∀ n, u n x₀ = 0) (hvnormal : ∀ n, v n x₀ = 0)
    (hT : ∀ n, Measurable (T n)) (hS : ∀ n, Measurable (S n))
    (hQ : ∀ n, Measurable (Q n)) (hR : ∀ n, Measurable (R n))
    (hQmem : ∀ n, ∀ᵐ y ∂μ, Q n y ∈ Y)
    (hRmem : ∀ n, ∀ᵐ y ∂ν, R n y ∈ Y)
    (hTpush : ∀ n, Measure.map (T n) (uniformMeasure K) = Measure.map (Q n) μ)
    (hSpush : ∀ n, Measure.map (S n) (uniformMeasure K) = Measure.map (R n) ν)
    (hTs : ∀ n, ∀ᵐ x ∂uniformMeasure K,
      ∀ z ∈ K, u n x + ⟪T n x, z - x⟫ ≤ u n z)
    (hSs : ∀ n, ∀ᵐ x ∂uniformMeasure K,
      ∀ z ∈ K, v n x + ⟪S n x, z - x⟫ ≤ v n z)
    {ε η : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n) (hη : ∀ n, 0 ≤ η n)
    (hεlim : Tendsto ε atTop (𝓝 0)) (hηlim : Tendsto η atTop (𝓝 0))
    (hQerr : ∀ n, ∀ᵐ y ∂μ, ‖Q n y - y‖ ≤ ε n)
    (hRerr : ∀ n, ∀ᵐ y ∂ν, ‖R n y - y‖ ≤ η n)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, mapL2Dist (uniformMeasure K) (T n) (S n) ≤
      C * Real.rpow (wasserstein2 (Measure.map (Q n) μ) (Measure.map (R n) ν))
        (1 / 3 : ℝ)) :
    ∃ Tμ Tν : E d → E d,
      IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
      mapL2Dist (uniformMeasure K) Tμ Tν ≤
        C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  have hQlim := ae_tendsto_of_quantization_error hεlim hQerr
  have hRlim := ae_tendsto_of_quantization_error hηlim hRerr
  obtain ⟨Tμ, φ, hφ, hTμ, hTμmem, _, hTμlim⟩ :=
    exists_uniqueOptimalMap_of_quantized_supporting_potentials
      hK hKconv hY hμ x₀ hx₀ u T Q L huLip huconv hunormal
      hT hQ hQmem hQlim hTpush hTs
  have hRφlim : ∀ᵐ y ∂ν,
      Tendsto (fun n => R (φ n) y) atTop (𝓝 y) := by
    filter_upwards [hRlim] with y hy
    exact hy.comp hφ.tendsto_atTop
  obtain ⟨Tν, ψ, hψ, hTν, hTνmem, _, hTνlim⟩ :=
    exists_uniqueOptimalMap_of_quantized_supporting_potentials
      hK hKconv hY hν x₀ hx₀ (fun n => v (φ n))
      (fun n => S (φ n)) (fun n => R (φ n)) L
      (fun n => hvLip (φ n)) (fun n => hvconv (φ n))
      (fun n => hvnormal (φ n)) (fun n => hS (φ n))
      (fun n => hR (φ n)) (fun n => hRmem (φ n)) hRφlim
      (fun n => hSpush (φ n)) (fun n => hSs (φ n))
  have hTmem : ∀ n, ∀ᵐ x ∂uniformMeasure K, T n x ∈ Y := by
    intro n
    apply ae_of_ae_map (hT n).aemeasurable
    rw [hTpush n]
    exact (ae_map_iff (hQ n).aemeasurable hY.measurableSet).mpr (hQmem n)
  have hSmem : ∀ n, ∀ᵐ x ∂uniformMeasure K, S n x ∈ Y := by
    intro n
    apply ae_of_ae_map (hS n).aemeasurable
    rw [hSpush n]
    exact (ae_map_iff (hR n).aemeasurable hY.measurableSet).mpr (hRmem n)
  obtain ⟨B, hB⟩ := hY.isBounded.exists_norm_le
  have hLp : ∀ F : E d → E d, Measurable F →
      (∀ᵐ x ∂uniformMeasure K, F x ∈ Y) → MemLp F 2 (uniformMeasure K) := by
    intro F hF hFY
    exact MemLp.of_bound hF.aestronglyMeasurable B (hFY.mono fun x hx => hB _ hx)
  have herrlim : Tendsto (fun n => ε (φ (ψ n)) + η (φ (ψ n)))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hεlim.add hηlim).comp (hφ.comp hψ).tendsto_atTop
  refine ⟨Tμ, Tν, hTμ, hTν, ?_⟩
  apply StabilityLimit.one_third_bound_of_target_approximation
    (hLp Tμ hTμ.1.1 hTμmem) (hLp Tν hTν.1.1 hTνmem)
    (fun n => hLp (T (φ (ψ n))) (hT _) (hTmem _))
    (fun n => hLp (S (φ (ψ n))) (hS _) (hSmem _))
    (hTμlim.comp hψ.tendsto_atTop) hTνlim hC herrlim
    (μₙ := fun n => Measure.map (Q (φ (ψ n))) μ)
    (νₙ := fun n => Measure.map (R (φ (ψ n))) ν)
  · intro n
    simpa only [add_assoc] using wasserstein2_map_le_of_compact hY hY hμ hν
      (hQ (φ (ψ n))) (hR (φ (ψ n))) (hε _) (hη _) (hQerr _) (hRerr _)
  · exact fun n => hbound (φ (ψ n))

end Problem358

namespace Problem358

/-- Finite-target stability is the sole quantitative input needed for the full
compact-target conclusion. The finite hypothesis only asks for some pair of
optimal maps; uniqueness transfers its estimate to the constructed potentials. -/
theorem one_third_stability_of_finite_targets
    {d : ℕ} {K Y : Set (E d)}
    (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hY : IsCompact Y) (hYne : Y.Nonempty)
    {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (∃ F : Set (E d), F.Finite ∧ F ⊆ Y ∧ IsSupported μ F) →
      (∃ G : Set (E d), G.Finite ∧ G ⊆ Y ∧ IsSupported ν G) →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
        mapL2Dist (uniformMeasure K) Tμ Tν ≤
          C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ)) :
    ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      IsSupported μ Y → IsSupported ν Y →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
        mapL2Dist (uniformMeasure K) Tμ Tν ≤
          C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  classical
  intro μ ν hμprob hνprob hμ hν
  let : IsProbabilityMeasure μ := hμprob
  let : IsProbabilityMeasure ν := hνprob
  let : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hKint
  let x₀ : E d := hKint.choose
  have hx₀ : x₀ ∈ interior K := hKint.choose_spec
  have hx₀K : x₀ ∈ K := interior_subset hx₀
  obtain ⟨B, hBpos, hB⟩ := hY.isBounded.exists_pos_norm_le
  let L : ℝ≥0 := ⟨B, hBpos.le⟩
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose Q hQY hQerr using fun n => exists_compact_quantizer hY hYne (hεpos n)
  have hQrange : ∀ n, Set.range (Q n) ⊆ Y := by
    intro n y hy
    obtain ⟨x, rfl⟩ := hy
    exact hQY n x
  have hμn : ∀ n, IsProbabilityMeasure (Measure.map (Q n) μ) :=
    fun n => (Measure.isProbabilityMeasure_map_iff (Q n).measurable.aemeasurable).mpr
      inferInstance
  have hνn : ∀ n, IsProbabilityMeasure (Measure.map (Q n) ν) :=
    fun n => (Measure.isProbabilityMeasure_map_iff (Q n).measurable.aemeasurable).mpr
      inferInstance
  have hpotμ : ∀ n, ∃ (u : E d → ℝ) (T : E d → E d),
      IsUniqueQuadraticOptimalMap (uniformMeasure K) (Measure.map (Q n) μ) T ∧
      ConvexOn ℝ Set.univ u ∧ LipschitzWith L u ∧ u x₀ = 0 ∧
      (∀ x, T x ∈ Y) ∧ ∀ x z, u x + ⟪T x, z - x⟫ ≤ u z := by
    intro n
    let := hμn n
    exact exists_uniform_finite_map_and_potential K hK hKint
      (Measure.map (Q n) μ) (Q n).finite_range (hQrange n)
      (simpleFunc_map_finite_support μ (Q n)).2 L hB x₀
  have hpotν : ∀ n, ∃ (v : E d → ℝ) (S : E d → E d),
      IsUniqueQuadraticOptimalMap (uniformMeasure K) (Measure.map (Q n) ν) S ∧
      ConvexOn ℝ Set.univ v ∧ LipschitzWith L v ∧ v x₀ = 0 ∧
      (∀ x, S x ∈ Y) ∧ ∀ x z, v x + ⟪S x, z - x⟫ ≤ v z := by
    intro n
    let := hνn n
    exact exists_uniform_finite_map_and_potential K hK hKint
      (Measure.map (Q n) ν) (Q n).finite_range (hQrange n)
      (simpleFunc_map_finite_support ν (Q n)).2 L hB x₀
  choose u T hTu huconv huLip hunormal hTY hTs using hpotμ
  choose v S hSu hvconv hvLip hvnormal hSY hSs using hpotν
  have hbound : ∀ n, mapL2Dist (uniformMeasure K) (T n) (S n) ≤
      C * Real.rpow (wasserstein2 (Measure.map (Q n) μ) (Measure.map (Q n) ν))
        (1 / 3 : ℝ) := by
    intro n
    obtain ⟨T', S', hT', hS', hb⟩ := hfinite (Measure.map (Q n) μ)
      (Measure.map (Q n) ν) (hμn n) (hνn n)
      ⟨Set.range (Q n), (Q n).finite_range, hQrange n,
        (simpleFunc_map_finite_support μ (Q n)).2⟩
      ⟨Set.range (Q n), (Q n).finite_range, hQrange n,
        (simpleFunc_map_finite_support ν (Q n)).2⟩
    rw [mapL2Dist_eq_of_optimal_maps (hTu n) (hSu n) hT'.1 hS'.1]
    exact hb
  have hQμerr : ∀ n, ∀ᵐ y ∂μ, ‖Q n y - y‖ ≤ ε n := by
    intro n
    filter_upwards [show ∀ᵐ y ∂μ, y ∈ Y from ae_iff.mpr hμ] with y hy
    simpa only [dist_eq_norm] using (hQerr n y hy).le
  have hQνerr : ∀ n, ∀ᵐ y ∂ν, ‖Q n y - y‖ ≤ ε n := by
    intro n
    filter_upwards [show ∀ᵐ y ∂ν, y ∈ Y from ae_iff.mpr hν] with y hy
    simpa only [dist_eq_norm] using (hQerr n y hy).le
  exact exists_uniqueOptimal_pair_of_quantized_stability hK hKconv hY x₀ hx₀K hμ hν
    u v T S (fun n => Q n) (fun n => Q n) L
    (fun n => (huLip n).lipschitzOnWith) (fun n => (hvLip n).lipschitzOnWith)
    (fun n => (huconv n).subset (Set.subset_univ K) hKconv)
    (fun n => (hvconv n).subset (Set.subset_univ K) hKconv)
    hunormal hvnormal (fun n => (hTu n).1.1) (fun n => (hSu n).1.1)
    (fun n => (Q n).measurable) (fun n => (Q n).measurable)
    (fun n => ae_of_all _ (hQY n)) (fun n => ae_of_all _ (hQY n))
    (fun n => (hTu n).1.2.1) (fun n => (hSu n).1.2.1)
    (fun n => ae_of_all _ fun x z _ => hTs n x z)
    (fun n => ae_of_all _ fun x z _ => hSs n x z)
    (fun n => (hεpos n).le) (fun n => (hεpos n).le)
    hεlim hεlim hQμerr hQνerr hC hbound

end Problem358

end

end OAI
