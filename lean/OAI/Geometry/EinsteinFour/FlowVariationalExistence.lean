import OAI.Geometry.EinsteinFour.FlowDifferentiability

namespace OAI

/-! Jointly continuous local solutions of the actual augmented variational
ODE. Only a C² vector field and ordinary Picard existence are used. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set Metric
open scoped ContDiff Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev VariationSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E × (E →L[ℝ] E)

def variationalField (f : E → E) (q : VariationSpace E) : VariationSpace E :=
  (f q.1, (fderiv ℝ f q.1).comp q.2)

omit [CompleteSpace E] in
theorem variationalField_contDiffAt (f : E → E) (q : VariationSpace E)
    (hf : ContDiffAt ℝ 2 f q.1) : ContDiffAt ℝ 1 (variationalField f) q := by
  have hD : ContDiffAt ℝ 1 (fderiv ℝ f) q.1 := hf.fderiv_right (by norm_num)
  exact ((hf.of_le (by norm_num)).comp q contDiffAt_fst).prodMk
    ((hD.comp q contDiffAt_fst).clm_comp contDiffAt_snd)

/-- A common local interval and continuous parameter dependence for the
base trajectory and its first variational linear map. -/
theorem exists_continuous_local_variational_flow (f : E → E) (p : E)
    (hf : ContDiffAt ℝ 2 f p) (U : Set E) (hU : U ∈ 𝓝 p) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ β : E × ℝ → VariationSpace E,
      ContinuousOn β (closedBall p r ×ˢ Ioo (-ε) ε) ∧
      ∀ q ∈ closedBall p r,
        β (q, 0) = (q, ContinuousLinearMap.id ℝ E) ∧
        ∀ t ∈ Ioo (-ε) ε, (β (q, t)).1 ∈ U ∧
          HasDerivAt (fun s => β (q, s)) (variationalField f (β (q, t))) t := by
  let p₀ : VariationSpace E := (p, ContinuousLinearMap.id ℝ E)
  obtain ⟨ε₀, hε₀, a, r₀, L, K, hr₀, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one (variationalField_contDiffAt f p₀ hf)
  obtain ⟨α, hα, hαc⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  let β : E × ℝ → VariationSpace E := fun qt =>
    α ((qt.1, ContinuousLinearMap.id ℝ E), qt.2)
  have hinit (q : E) (hq : q ∈ closedBall p (r₀ : ℝ)) :
      (q, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ (r₀ : ℝ) := by
    simpa only [mem_closedBall, p₀, Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hq
  have hβc : ContinuousOn β (closedBall p (r₀ : ℝ) ×ˢ Icc (0 - ε₀) (0 + ε₀)) := by
    exact hαc.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd).continuousOn
      (fun qt hqt => ⟨hinit qt.1 hqt.1, hqt.2⟩)
  have hβ0 : β (p, 0) = p₀ := (hα p₀ (mem_closedBall_self (by positivity))).1
  have hr₀' : 0 < (r₀ : ℝ) := hr₀
  have hn : closedBall p (r₀ : ℝ) ×ˢ Icc (0 - ε₀) (0 + ε₀) ∈ 𝓝 (p, (0 : ℝ)) :=
    by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (closedBall_mem_nhds p hr₀')
        (Icc_mem_nhds (by linarith) (by linarith))
  have hnear : ∀ᶠ qt in 𝓝 (p, (0 : ℝ)), (β qt).1 ∈ U :=
    (hβc.continuousAt hn).fst.preimage_mem_nhds (by simpa only [hβ0, p₀] using hU)
  obtain ⟨δ, hδ, hδnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let r : ℝ := min (r₀ : ℝ) (δ / 2)
  let ε : ℝ := min ε₀ (δ / 2)
  have hr : 0 < r := lt_min hr₀' (half_pos hδ)
  have hε : 0 < ε := lt_min hε₀ (half_pos hδ)
  have hsub {q : E} (hq : q ∈ closedBall p r) : q ∈ closedBall p (r₀ : ℝ) :=
    closedBall_subset_closedBall (min_le_left _ _) hq
  have htime {t : ℝ} (ht : t ∈ Ioo (-ε) ε) : t ∈ Ioo (0 - ε₀) (0 + ε₀) := by
    have hle : ε ≤ ε₀ := min_le_left _ _
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨r, hr, ε, hε, β, hβc.mono ?_, fun q hq => ⟨(hα _ (hinit q (hsub hq))).1, ?_⟩⟩
  · rintro ⟨q, t⟩ ⟨hq, ht⟩
    exact ⟨hsub hq, Ioo_subset_Icc_self (htime ht)⟩
  · intro t ht
    constructor
    · apply hδnear
      rw [Prod.dist_eq, max_lt_iff]
      constructor
      · have hqr : dist q p ≤ r := hq
        have hrd : r ≤ δ / 2 := min_le_right _ _
        linarith
      · rw [Real.dist_eq, sub_zero, abs_lt]
        have hεd : ε ≤ δ / 2 := min_le_right _ _
        constructor <;> linarith [ht.1, ht.2]
    · exact ((hα _ (hinit q (hsub hq))).2 t (Ioo_subset_Icc_self (htime ht))).hasDerivAt
        (Icc_mem_nhds (htime ht).1 (htime ht).2)

end
end PositiveEinsteinFour.FlowCalculus

end OAI
