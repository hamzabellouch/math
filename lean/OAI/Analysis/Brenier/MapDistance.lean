import OAI.Analysis.Brenier.Basic

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ} {ρ : Measure (E d)} {T S U : E d → E d}

@[simp] theorem mapL2Dist_self (ρ : Measure (E d)) (T : E d → E d) :
    mapL2Dist ρ T T = 0 := by
  simp [mapL2Dist]

theorem mapL2Dist_nonneg (ρ : Measure (E d)) (T S : E d → E d) :
    0 ≤ mapL2Dist ρ T S := Real.sqrt_nonneg _

theorem mapL2Dist_comm (ρ : Measure (E d)) (T S : E d → E d) :
    mapL2Dist ρ T S = mapL2Dist ρ S T := by
  simp only [mapL2Dist, norm_sub_rev (T _) (S _)]

theorem mapL2Dist_congr_ae {T' S' : E d → E d}
    (hT : T =ᵐ[ρ] T') (hS : S =ᵐ[ρ] S') :
    mapL2Dist ρ T S = mapL2Dist ρ T' S' := by
  unfold mapL2Dist
  congr 1
  apply integral_congr_ae
  filter_upwards [hT, hS] with x hx hy
  rw [hx, hy]

theorem mapL2Dist_eq_zero_of_ae_eq (h : T =ᵐ[ρ] S) :
    mapL2Dist ρ T S = 0 := by
  rw [mapL2Dist_congr_ae h (Filter.EventuallyEq.refl _ _), mapL2Dist_self]

theorem mapL2Dist_sq (ρ : Measure (E d)) (T S : E d → E d) :
    mapL2Dist ρ T S ^ 2 = ∫ x, ‖T x - S x‖ ^ 2 ∂ρ := by
  exact Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)

theorem mapL2Dist_eq_zero_iff
    (hInt : Integrable (fun x => ‖T x - S x‖ ^ 2) ρ) :
    mapL2Dist ρ T S = 0 ↔ T =ᵐ[ρ] S := by
  constructor
  · intro h
    have hIntegral : (∫ x, ‖T x - S x‖ ^ 2 ∂ρ) = 0 := by
      rw [← mapL2Dist_sq, h]
      simp
    have ha := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hInt).mp hIntegral
    filter_upwards [ha] with x hx
    simpa only [Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] using hx
  · exact mapL2Dist_eq_zero_of_ae_eq

theorem quadraticPlanCost_map_pair (hT : Measurable T) (hS : Measurable S) :
    quadraticPlanCost (Measure.map (fun x => (T x, S x)) ρ) =
      ∫⁻ x, ENNReal.ofReal (‖T x - S x‖ ^ 2) ∂ρ := by
  unfold quadraticPlanCost
  exact lintegral_map (by fun_prop) (hT.prodMk hS)

theorem mapL2Dist_eq_sqrt_pair_cost (hT : Measurable T) (hS : Measurable S) :
    mapL2Dist ρ T S = Real.sqrt
      (quadraticPlanCost (Measure.map (fun x => (T x, S x)) ρ)).toReal := by
  rw [mapL2Dist, quadraticPlanCost_map_pair hT hS]
  congr 1
  apply integral_eq_lintegral_of_nonneg_ae
  · exact ae_of_all _ fun x => sq_nonneg _
  · fun_prop

theorem mapL2Dist_eq_lpNorm (hT : AEStronglyMeasurable T ρ)
    (hS : AEStronglyMeasurable S ρ) :
    mapL2Dist ρ T S = lpNorm (T - S) 2 ρ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) (hT.sub hS)]
  simp [mapL2Dist, Real.sqrt_eq_rpow]

theorem mapL2Dist_eq_dist_toLp (hT : MemLp T 2 ρ) (hS : MemLp S 2 ρ) :
    mapL2Dist ρ T S = dist (hT.toLp T) (hS.toLp S) := by
  rw [Lp.dist_edist, Lp.edist_toLp_toLp, toReal_eLpNorm]
  exact mapL2Dist_eq_lpNorm hT.aestronglyMeasurable hS.aestronglyMeasurable

theorem mapL2Dist_triangle (hT : MemLp T 2 ρ) (hS : MemLp S 2 ρ)
    (hU : MemLp U 2 ρ) :
    mapL2Dist ρ T U ≤ mapL2Dist ρ T S + mapL2Dist ρ S U := by
  rw [mapL2Dist_eq_dist_toLp hT hU, mapL2Dist_eq_dist_toLp hT hS,
    mapL2Dist_eq_dist_toLp hS hU]
  exact dist_triangle _ _ _

end Problem358

namespace Problem358

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- A bounded nonnegative squared separation is integrable against a finite measure. -/
theorem integrable_norm_sub_sq_of_ae_bound {ρ : Measure X} [IsFiniteMeasure ρ]
    {T S : X → V} (hT : Measurable T) (hS : Measurable S)
    {R : ℝ} (hbound : ∀ᵐ x ∂ρ, ‖T x - S x‖ ≤ R) :
    Integrable (fun x => ‖T x - S x‖ ^ 2) ρ := by
  refine (integrable_const (R ^ 2)).mono' ?_ ?_
  · exact ((hT.sub hS).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2

omit [NormedAddCommGroup V] [BorelSpace V] [SecondCountableTopology V] in
/-- Support of a pushforward pulls back to an almost-everywhere range condition. -/
theorem ae_mem_of_map_compl_eq_zero {ρ : Measure X} {T : X → V}
    (hT : Measurable T) {Y : Set V} (hY : (Measure.map T ρ) Yᶜ = 0) :
    ∀ᵐ x ∂ρ, T x ∈ Y := by
  apply ae_of_ae_map hT.aemeasurable
  exact ae_iff.mpr hY

/-- Two measurable maps with essentially bounded ranges have integrable squared separation. -/
theorem integrable_norm_sub_sq_of_ae_mem_bounded {ρ : Measure X} [IsFiniteMeasure ρ]
    {T S : X → V} (hT : Measurable T) (hS : Measurable S)
    {Y Z : Set V} (hY : Bornology.IsBounded Y) (hZ : Bornology.IsBounded Z)
    (hTY : ∀ᵐ x ∂ρ, T x ∈ Y) (hSZ : ∀ᵐ x ∂ρ, S x ∈ Z) :
    Integrable (fun x => ‖T x - S x‖ ^ 2) ρ := by
  obtain ⟨R, hR⟩ := hY.exists_norm_le
  obtain ⟨Q, hQ⟩ := hZ.exists_norm_le
  apply integrable_norm_sub_sq_of_ae_bound hT hS (R := R + Q)
  filter_upwards [hTY, hSZ] with x hx hy
  exact (norm_sub_le _ _).trans (add_le_add (hR _ hx) (hQ _ hy))

/-- Compact support of the two pushforwards suffices for the L² separation integral. -/
theorem integrable_norm_sub_sq_of_map_compact {ρ : Measure X} [IsFiniteMeasure ρ]
    {T S : X → V} (hT : Measurable T) (hS : Measurable S)
    {Y Z : Set V} (hY : IsCompact Y) (hZ : IsCompact Z)
    (hTY : (Measure.map T ρ) Yᶜ = 0) (hSZ : (Measure.map S ρ) Zᶜ = 0) :
    Integrable (fun x => ‖T x - S x‖ ^ 2) ρ :=
  integrable_norm_sub_sq_of_ae_mem_bounded hT hS hY.isBounded hZ.isBounded
    (ae_mem_of_map_compl_eq_zero hT hTY) (ae_mem_of_map_compl_eq_zero hS hSZ)

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- The squared L² separation integral vanishes exactly for a.e.-equal maps. -/
theorem integral_norm_sub_sq_eq_zero_iff {ρ : Measure X} {T S : X → V}
    (hTS : Integrable (fun x => ‖T x - S x‖ ^ 2) ρ) :
    (∫ x, ‖T x - S x‖ ^ 2 ∂ρ) = 0 ↔ T =ᵐ[ρ] S := by
  rw [integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hTS]
  simp only [Filter.EventuallyEq, Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem358

variable {d : ℕ} {ρ : Measure (E d)}

theorem exists_mapL2Dist_limit {T : ℕ → E d → E d}
    (hT : ∀ n, MemLp (T n) 2 ρ)
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      mapL2Dist ρ (T m) (T n) < ε) :
    ∃ S : E d → E d, Measurable S ∧ MemLp S 2 ρ ∧
      Tendsto (fun n => mapL2Dist ρ (T n) S) atTop (𝓝 0) := by
  let F : ℕ → Lp (E d) 2 ρ := fun n => (hT n).toLp (T n)
  have hCF : CauchySeq F := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [F, ← mapL2Dist_eq_dist_toLp] using hN m hm n hn
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete hCF
  refine ⟨S, (Lp.stronglyMeasurable S).measurable, (Lp.memLp S), ?_⟩
  have hDist := tendsto_iff_dist_tendsto_zero.mp hS
  simpa only [mapL2Dist_eq_dist_toLp (hT _) (Lp.memLp S), Lp.toLp_coeFn, F]
    using hDist

theorem exists_subseq_tendsto_ae_of_mapL2Dist_tendsto_zero
    {T : ℕ → E d → E d} {S : E d → E d}
    (hT : ∀ n, MemLp (T n) 2 ρ) (hS : MemLp S 2 ρ)
    (hlim : Tendsto (fun n => mapL2Dist ρ (T n) S) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂ρ, Tendsto (fun n => T (ns n) x) atTop (𝓝 (S x)) := by
  let F : ℕ → Lp (E d) 2 ρ := fun n => (hT n).toLp (T n)
  have hLp : Tendsto F atTop (𝓝 (hS.toLp S)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [F, ← mapL2Dist_eq_dist_toLp] using hlim
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hLp).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have hEq : ∀ᵐ x ∂ρ, ∀ n, F n x = T n x := by
    exact ae_all_iff.mpr (fun n => (hT n).coeFn_toLp)
  filter_upwards [hae, hEq, hS.coeFn_toLp] with x hx hTx hSx
  simpa only [hTx, hSx] using hx

theorem ae_mem_of_mapL2Dist_tendsto_zero
    {T : ℕ → E d → E d} {S : E d → E d} {Y : Set (E d)}
    (hT : ∀ n, MemLp (T n) 2 ρ) (hS : MemLp S 2 ρ)
    (hlim : Tendsto (fun n => mapL2Dist ρ (T n) S) atTop (𝓝 0))
    (hY : IsClosed Y) (hmem : ∀ n, ∀ᵐ x ∂ρ, T n x ∈ Y) :
    ∀ᵐ x ∂ρ, S x ∈ Y := by
  obtain ⟨ns, _, hns⟩ :=
    exists_subseq_tendsto_ae_of_mapL2Dist_tendsto_zero hT hS hlim
  have hAll : ∀ᵐ x ∂ρ, ∀ n, T n x ∈ Y := ae_all_iff.mpr hmem
  filter_upwards [hns, hAll] with x hx hTx
  exact hY.mem_of_tendsto hx (Eventually.of_forall fun n => hTx (ns n))

theorem exists_mapL2Dist_limit_in_closed {T : ℕ → E d → E d} {Y : Set (E d)}
    (hT : ∀ n, MemLp (T n) 2 ρ)
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      mapL2Dist ρ (T m) (T n) < ε)
    (hY : IsClosed Y) (hmem : ∀ n, ∀ᵐ x ∂ρ, T n x ∈ Y) :
    ∃ S : E d → E d, Measurable S ∧ MemLp S 2 ρ ∧
      (∀ᵐ x ∂ρ, S x ∈ Y) ∧
      Tendsto (fun n => mapL2Dist ρ (T n) S) atTop (𝓝 0) := by
  obtain ⟨S, hSm, hS, hlim⟩ := exists_mapL2Dist_limit hT hC
  exact ⟨S, hSm, hS, ae_mem_of_mapL2Dist_tendsto_zero hT hS hlim hY hmem, hlim⟩

/-- Map distance is continuous under L² convergence of each endpoint. -/
theorem tendsto_mapL2Dist_of_tendsto {ι : Type*} {l : Filter ι}
    {T S : ι → E d → E d} {T₀ S₀ : E d → E d}
    (hT : ∀ n, MemLp (T n) 2 ρ) (hS : ∀ n, MemLp (S n) 2 ρ)
    (hT₀ : MemLp T₀ 2 ρ) (hS₀ : MemLp S₀ 2 ρ)
    (hTlim : Tendsto (fun n => mapL2Dist ρ (T n) T₀) l (𝓝 0))
    (hSlim : Tendsto (fun n => mapL2Dist ρ (S n) S₀) l (𝓝 0)) :
    Tendsto (fun n => mapL2Dist ρ (T n) (S n)) l (𝓝 (mapL2Dist ρ T₀ S₀)) := by
  have hTLp : Tendsto (fun n => (hT n).toLp (T n)) l (𝓝 (hT₀.toLp T₀)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [← mapL2Dist_eq_dist_toLp] using hTlim
  have hSLp : Tendsto (fun n => (hS n).toLp (S n)) l (𝓝 (hS₀.toLp S₀)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [← mapL2Dist_eq_dist_toLp] using hSlim
  simpa only [← mapL2Dist_eq_dist_toLp] using hTLp.dist hSLp

end Problem358

end

noncomputable section
open MeasureTheory

namespace Problem358

/-- The graph plan of a measurable map remembers its almost-everywhere class. -/
theorem graphPlan_eq_iff_ae_eq {d : ℕ} {ρ : Measure (E d)}
    {T S : E d → E d} (hT : Measurable T) (hS : Measurable S) :
    graphPlan ρ T = graphPlan ρ S ↔ T =ᵐ[ρ] S := by
  constructor
  · intro heq
    have hgraph : ∀ᵐ p ∂graphPlan ρ T, p.2 = T p.1 := by
      apply (ae_map_iff (measurable_id.prodMk hT).aemeasurable
        (measurableSet_eq_fun measurable_snd (hT.comp measurable_fst))).2
      exact Filter.Eventually.of_forall fun _ => rfl
    rw [heq] at hgraph
    have hae := ae_of_ae_map (measurable_id.prodMk hS).aemeasurable hgraph
    filter_upwards [hae] with x hx
    exact hx.symm
  · intro hae
    apply Measure.map_congr
    filter_upwards [hae] with x hx
    exact Prod.ext rfl hx

/-- A measurable transport of a probability source defines a coupling with its law. -/
theorem graphPlan_isCoupling {d : ℕ} {ρ μ : Measure (E d)}
    [IsProbabilityMeasure ρ] {T : E d → E d}
    (hT : Measurable T) (hlaw : Measure.map T ρ = μ) :
    IsCoupling ρ μ (graphPlan ρ T) := by
  have hm : Measurable (fun x => (x, T x)) := measurable_id.prodMk hT
  refine ⟨?_, ?_, ?_⟩
  · unfold graphPlan
    infer_instance
  · rw [graphPlan, Measure.map_map measurable_fst hm]
    exact Measure.map_id
  · rw [graphPlan, Measure.map_map measurable_snd hm]
    exact hlaw

/-- All optimal maps for the same source and target have the same graph cost. -/
theorem IsQuadraticOptimalMap.cost_eq {d : ℕ} {ρ μ : Measure (E d)}
    [IsProbabilityMeasure ρ] {T S : E d → E d}
    (hT : IsQuadraticOptimalMap ρ μ T) (hS : IsQuadraticOptimalMap ρ μ S) :
    quadraticPlanCost (graphPlan ρ T) = quadraticPlanCost (graphPlan ρ S) := by
  apply le_antisymm
  · exact hT.2.2 _ (graphPlan_isCoupling hS.1 hS.2.1)
  · exact hS.2.2 _ (graphPlan_isCoupling hT.1 hT.2.1)

/-- Uniqueness among transport plans implies uniqueness of the map almost everywhere. -/
theorem IsUniqueQuadraticOptimalMap.ae_eq_of_optimal {d : ℕ}
    {ρ μ : Measure (E d)} [IsProbabilityMeasure ρ] {T S : E d → E d}
    (hT : IsUniqueQuadraticOptimalMap ρ μ T)
    (hS : IsQuadraticOptimalMap ρ μ S) : T =ᵐ[ρ] S := by
  apply (graphPlan_eq_iff_ae_eq hT.1.1 hS.1).mp
  exact (hT.2 _ (graphPlan_isCoupling hS.1 hS.2.1)
    (hS.2.2 _ (graphPlan_isCoupling hT.1.1 hT.1.2.1))).symm

/-- Distances between unique optimal maps do not depend on selected representatives. -/
theorem mapL2Dist_eq_of_optimal_maps {d : ℕ} {ρ μ ν : Measure (E d)}
    [IsProbabilityMeasure ρ] {T S T' S' : E d → E d}
    (hT : IsUniqueQuadraticOptimalMap ρ μ T)
    (hS : IsUniqueQuadraticOptimalMap ρ ν S)
    (hT' : IsQuadraticOptimalMap ρ μ T') (hS' : IsQuadraticOptimalMap ρ ν S') :
    mapL2Dist ρ T S = mapL2Dist ρ T' S' :=
  mapL2Dist_congr_ae (hT.ae_eq_of_optimal hT') (hS.ae_eq_of_optimal hS')

/-- Changing a measurable representative on a null set preserves optimality. -/
theorem IsQuadraticOptimalMap.congr_ae {d : ℕ} {ρ μ : Measure (E d)}
    {T S : E d → E d} (hT : IsQuadraticOptimalMap ρ μ T)
    (hS : Measurable S) (hae : T =ᵐ[ρ] S) : IsQuadraticOptimalMap ρ μ S := by
  have hg := (graphPlan_eq_iff_ae_eq hT.1 hS).mpr hae
  refine ⟨hS, ?_, ?_⟩
  · exact (Measure.map_congr hae).symm.trans hT.2.1
  · intro π hπ
    rw [← hg]
    exact hT.2.2 π hπ

/-- Changing a measurable representative on a null set also preserves plan uniqueness. -/
theorem IsUniqueQuadraticOptimalMap.congr_ae {d : ℕ} {ρ μ : Measure (E d)}
    {T S : E d → E d} (hT : IsUniqueQuadraticOptimalMap ρ μ T)
    (hS : Measurable S) (hae : T =ᵐ[ρ] S) :
    IsUniqueQuadraticOptimalMap ρ μ S := by
  have hg := (graphPlan_eq_iff_ae_eq hT.1.1 hS).mpr hae
  refine ⟨hT.1.congr_ae hS hae, ?_⟩
  intro π hπ hcost
  rw [← hg] at hcost ⊢
  exact hT.2 π hπ hcost

end Problem358

end

noncomputable section
open Filter
open scoped Topology

namespace Problem358.StabilityLimit

/-- A uniform power bound survives convergence when the input distances have only
an asymptotic upper bound. This is enough for finite-target quantization. -/
theorem real_bound_of_approximation
    {D W C α : ℝ} {Dₙ Wₙ ε : ℕ → ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hWₙ : ∀ n, 0 ≤ Wₙ n)
    (hD : Tendsto Dₙ atTop (𝓝 D)) (hε : Tendsto ε atTop (𝓝 0))
    (hupper : ∀ n, Wₙ n ≤ W + ε n)
    (hbound : ∀ n, Dₙ n ≤ C * Real.rpow (Wₙ n) α) :
    D ≤ C * Real.rpow W α := by
  have hinput : Tendsto (fun n => W + ε n) atTop (𝓝 W) := by
    simpa using tendsto_const_nhds.add hε
  have hpower : Tendsto (fun n => C * Real.rpow (W + ε n) α)
      atTop (𝓝 (C * Real.rpow W α)) :=
    tendsto_const_nhds.mul ((Real.continuous_rpow_const hα).tendsto W |>.comp hinput)
  apply le_of_tendsto_of_tendsto hD hpower
  exact Filter.Eventually.of_forall fun n => (hbound n).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hWₙ n) (hupper n) hα) hC)

/-- Metric version of the approximation closure step. -/
theorem dist_bound_of_approximation {X : Type*} [PseudoMetricSpace X]
    {x y : X} {xₙ yₙ : ℕ → X} {W C α : ℝ} {Wₙ ε : ℕ → ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hWₙ : ∀ n, 0 ≤ Wₙ n)
    (hx : Tendsto xₙ atTop (𝓝 x)) (hy : Tendsto yₙ atTop (𝓝 y))
    (hε : Tendsto ε atTop (𝓝 0)) (hupper : ∀ n, Wₙ n ≤ W + ε n)
    (hbound : ∀ n, dist (xₙ n) (yₙ n) ≤ C * Real.rpow (Wₙ n) α) :
    dist x y ≤ C * Real.rpow W α := by
  exact real_bound_of_approximation hC hα hWₙ (hx.dist hy) hε hupper hbound

/-- The exact exponent used by the stability target. -/
theorem one_third_dist_bound_of_approximation {X : Type*} [PseudoMetricSpace X]
    {x y : X} {xₙ yₙ : ℕ → X} {W C : ℝ} {Wₙ ε : ℕ → ℝ}
    (hC : 0 ≤ C) (hWₙ : ∀ n, 0 ≤ Wₙ n)
    (hx : Tendsto xₙ atTop (𝓝 x)) (hy : Tendsto yₙ atTop (𝓝 y))
    (hε : Tendsto ε atTop (𝓝 0)) (hupper : ∀ n, Wₙ n ≤ W + ε n)
    (hbound : ∀ n, dist (xₙ n) (yₙ n) ≤ C * Real.rpow (Wₙ n) (1 / 3 : ℝ)) :
    dist x y ≤ C * Real.rpow W (1 / 3 : ℝ) := by
  exact dist_bound_of_approximation hC (by norm_num) hWₙ hx hy hε hupper hbound

open MeasureTheory
variable {d : ℕ} {ρ : Measure (E d)}

/-- Strong L² convergence in both arguments gives convergence of the map distance. -/
theorem tendsto_mapL2Dist {T S : E d → E d} {Tₙ Sₙ : ℕ → E d → E d}
    (hT : MemLp T 2 ρ) (hS : MemLp S 2 ρ)
    (hTₙ : ∀ n, MemLp (Tₙ n) 2 ρ) (hSₙ : ∀ n, MemLp (Sₙ n) 2 ρ)
    (hlimT : Tendsto (fun n => mapL2Dist ρ (Tₙ n) T) atTop (𝓝 0))
    (hlimS : Tendsto (fun n => mapL2Dist ρ (Sₙ n) S) atTop (𝓝 0)) :
    Tendsto (fun n => mapL2Dist ρ (Tₙ n) (Sₙ n)) atTop (𝓝 (mapL2Dist ρ T S)) := by
  have hTLp : Tendsto (fun n => (hTₙ n).toLp (Tₙ n)) atTop (𝓝 (hT.toLp T)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [← mapL2Dist_eq_dist_toLp] using hlimT
  have hSLp : Tendsto (fun n => (hSₙ n).toLp (Sₙ n)) atTop (𝓝 (hS.toLp S)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [← mapL2Dist_eq_dist_toLp] using hlimS
  simpa only [← mapL2Dist_eq_dist_toLp] using hTLp.dist hSLp

/-- Passage from finite-target map bounds to a strong-L² limiting pair. -/
theorem mapL2Dist_bound_of_approximation
    {T S : E d → E d} {Tₙ Sₙ : ℕ → E d → E d}
    {W C α : ℝ} {Wₙ ε : ℕ → ℝ}
    (hT : MemLp T 2 ρ) (hS : MemLp S 2 ρ)
    (hTₙ : ∀ n, MemLp (Tₙ n) 2 ρ) (hSₙ : ∀ n, MemLp (Sₙ n) 2 ρ)
    (hlimT : Tendsto (fun n => mapL2Dist ρ (Tₙ n) T) atTop (𝓝 0))
    (hlimS : Tendsto (fun n => mapL2Dist ρ (Sₙ n) S) atTop (𝓝 0))
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hWₙ : ∀ n, 0 ≤ Wₙ n)
    (hε : Tendsto ε atTop (𝓝 0)) (hupper : ∀ n, Wₙ n ≤ W + ε n)
    (hbound : ∀ n, mapL2Dist ρ (Tₙ n) (Sₙ n) ≤ C * Real.rpow (Wₙ n) α) :
    mapL2Dist ρ T S ≤ C * Real.rpow W α := by
  exact real_bound_of_approximation hC hα hWₙ
    (tendsto_mapL2Dist hT hS hTₙ hSₙ hlimT hlimS) hε hupper hbound

/-- Final one-third estimate under explicit finite approximation hypotheses. -/
theorem one_third_bound_of_target_approximation
    {T S : E d → E d} {Tₙ Sₙ : ℕ → E d → E d}
    {μ ν : Measure (E d)} {μₙ νₙ : ℕ → Measure (E d)} {C : ℝ} {ε : ℕ → ℝ}
    (hT : MemLp T 2 ρ) (hS : MemLp S 2 ρ)
    (hTₙ : ∀ n, MemLp (Tₙ n) 2 ρ) (hSₙ : ∀ n, MemLp (Sₙ n) 2 ρ)
    (hlimT : Tendsto (fun n => mapL2Dist ρ (Tₙ n) T) atTop (𝓝 0))
    (hlimS : Tendsto (fun n => mapL2Dist ρ (Sₙ n) S) atTop (𝓝 0))
    (hC : 0 ≤ C) (hε : Tendsto ε atTop (𝓝 0))
    (hupper : ∀ n, wasserstein2 (μₙ n) (νₙ n) ≤ wasserstein2 μ ν + ε n)
    (hbound : ∀ n, mapL2Dist ρ (Tₙ n) (Sₙ n) ≤
      C * Real.rpow (wasserstein2 (μₙ n) (νₙ n)) (1 / 3 : ℝ)) :
    mapL2Dist ρ T S ≤ C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  exact mapL2Dist_bound_of_approximation hT hS hTₙ hSₙ hlimT hlimS hC
    (by norm_num) (fun n => Real.sqrt_nonneg _) hε hupper hbound

end Problem358.StabilityLimit

end

noncomputable section
open MeasureTheory

namespace Problem358

/-- On a probability source, an essential pointwise distance bound is an L² bound. -/
theorem mapL2Dist_le_of_ae_bound {d : ℕ} {ρ : Measure (E d)}
    [IsProbabilityMeasure ρ] {T S : E d → E d}
    (hT : Measurable T) (hS : Measurable S) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂ρ, ‖T x - S x‖ ≤ M) :
    mapL2Dist ρ T S ≤ M := by
  apply (Real.sqrt_le_left hM).mpr
  have hi := integrable_norm_sub_sq_of_ae_bound hT hS hbound
  have hle : (∫ x, ‖T x - S x‖ ^ 2 ∂ρ) ≤ ∫ _x : E d, M ^ 2 ∂ρ := by
    apply integral_mono_ae hi (integrable_const _)
    filter_upwards [hbound] with x hx
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  simpa using hle

/-- Uniform norm bounds on two maps give a uniform L² distance bound. -/
theorem mapL2Dist_le_of_ae_norm_bounds {d : ℕ} {ρ : Measure (E d)}
    [IsProbabilityMeasure ρ] {T S : E d → E d}
    (hT : Measurable T) (hS : Measurable S) {R Q : ℝ}
    (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hRT : ∀ᵐ x ∂ρ, ‖T x‖ ≤ R) (hQS : ∀ᵐ x ∂ρ, ‖S x‖ ≤ Q) :
    mapL2Dist ρ T S ≤ R + Q := by
  apply mapL2Dist_le_of_ae_bound hT hS (add_nonneg hR hQ)
  filter_upwards [hRT, hQS] with x hx hy
  exact (norm_sub_le _ _).trans (add_le_add hx hy)

/-- The norms of optimal maps are controlled by a bound on the target supports. -/
theorem IsQuadraticOptimalMap.mapL2Dist_le_of_norm_bound {d : ℕ}
    {ρ μ ν : Measure (E d)} [IsProbabilityMeasure ρ]
    {T S : E d → E d}
    (hT : IsQuadraticOptimalMap ρ μ T) (hS : IsQuadraticOptimalMap ρ ν S)
    {Y : Set (E d)} (hμ : IsSupported μ Y) (hν : IsSupported ν Y)
    {L : ℝ} (hL : 0 ≤ L) (hY : ∀ y ∈ Y, ‖y‖ ≤ L) :
    mapL2Dist ρ T S ≤ 2 * L := by
  have hTY : ∀ᵐ x ∂ρ, T x ∈ Y :=
    ae_mem_of_map_compl_eq_zero hT.1 (by simpa [hT.2.1, IsSupported] using hμ)
  have hSY : ∀ᵐ x ∂ρ, S x ∈ Y :=
    ae_mem_of_map_compl_eq_zero hS.1 (by simpa [hS.2.1, IsSupported] using hν)
  have hRT : ∀ᵐ x ∂ρ, ‖T x‖ ≤ L := hTY.mono fun x hx => hY _ hx
  have hRS : ∀ᵐ x ∂ρ, ‖S x‖ ≤ L := hSY.mono fun x hx => hY _ hx
  simpa [two_mul] using mapL2Dist_le_of_ae_norm_bounds hT.1 hS.1 hL hL hRT hRS

end Problem358

namespace Problem358

/-- Compact support of the pushforwards suffices for separation by map distance. -/
theorem mapL2Dist_eq_zero_iff_ae_of_compact {d : ℕ} {ρ : Measure (E d)}
    [IsFiniteMeasure ρ] {T S : E d → E d} (hT : Measurable T) (hS : Measurable S)
    {Y Z : Set (E d)} (hY : IsCompact Y) (hZ : IsCompact Z)
    (hTY : IsSupported (Measure.map T ρ) Y) (hSZ : IsSupported (Measure.map S ρ) Z) :
    mapL2Dist ρ T S = 0 ↔ T =ᵐ[ρ] S :=
  mapL2Dist_eq_zero_iff (integrable_norm_sub_sq_of_map_compact hT hS hY hZ hTY hSZ)

/-- Positive map distance is equivalent to distinct a.e. classes under integrability. -/
theorem mapL2Dist_pos_iff_not_ae {d : ℕ} {ρ : Measure (E d)}
    {T S : E d → E d} (hTS : Integrable (fun x => ‖T x - S x‖ ^ 2) ρ) :
    0 < mapL2Dist ρ T S ↔ ¬ T =ᵐ[ρ] S := by
  rw [lt_iff_le_and_ne]
  simp only [mapL2Dist_nonneg, true_and, ne_eq, eq_comm (a := (0 : ℝ)),
    mapL2Dist_eq_zero_iff hTS]

/-- Two unequal target laws force positive map distance for compact-supported maps. -/
theorem mapL2Dist_pos_of_map_ne_of_compact {d : ℕ} {ρ : Measure (E d)}
    [IsFiniteMeasure ρ] {T S : E d → E d} (hT : Measurable T) (hS : Measurable S)
    {Y Z : Set (E d)} (hY : IsCompact Y) (hZ : IsCompact Z)
    (hTY : IsSupported (Measure.map T ρ) Y) (hSZ : IsSupported (Measure.map S ρ) Z)
    (hne : Measure.map T ρ ≠ Measure.map S ρ) : 0 < mapL2Dist ρ T S := by
  refine lt_of_le_of_ne (mapL2Dist_nonneg ρ T S) ?_
  intro hzero
  have hae : T =ᵐ[ρ] S :=
    (mapL2Dist_eq_zero_iff_ae_of_compact hT hS hY hZ hTY hSZ).mp hzero.symm
  exact hne (Measure.map_congr hae)

/-- Optimal maps to distinct compact-supported targets have positive map distance. -/
theorem IsQuadraticOptimalMap.mapL2Dist_pos_of_ne {d : ℕ}
    {ρ μ ν : Measure (E d)} [IsFiniteMeasure ρ] {T S : E d → E d}
    (hT : IsQuadraticOptimalMap ρ μ T) (hS : IsQuadraticOptimalMap ρ ν S)
    {Y Z : Set (E d)} (hY : IsCompact Y) (hZ : IsCompact Z)
    (hμ : IsSupported μ Y) (hν : IsSupported ν Z) (hne : μ ≠ ν) :
    0 < mapL2Dist ρ T S := by
  apply mapL2Dist_pos_of_map_ne_of_compact hT.1 hS.1 hY hZ
  · simpa only [hT.2.1] using hμ
  · simpa only [hS.2.1] using hν
  · simpa only [hT.2.1, hS.2.1] using hne

end Problem358

end

end OAI
