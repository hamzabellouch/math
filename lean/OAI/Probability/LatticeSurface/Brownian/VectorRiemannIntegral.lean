import Mathlib
import OAI.Probability.LatticeSurface.Brownian.VectorRiemannGeometry

namespace OAI

namespace ConvexSkorokhod

open Set Filter MeasureTheory

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ F] in
lemma variation_singleton_zero {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : VectorMeasure X F) (x : X) (hx : μ {x}=0) : μ.variation {x}=0 := by
  apply (VectorMeasure.variation_apply_eq_zero (MeasurableSet.singleton x)).mpr
  intro s hs hsm
  rcases s.eq_empty_or_nonempty with rfl|⟨y,hy⟩
  · simp
  · have hyx : y=x := Set.mem_singleton_iff.mp (hs hy)
    have he : s={x} := subset_antisymm hs (singleton_subset_iff.mpr (hyx ▸ hy))
    simpa only [he] using hx

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma vectorStep_integrable (μ : VectorMeasure unitInterval F) [IsFiniteMeasure μ.variation]
    (f : unitInterval → E) (m : ℕ) : μ.Integrable (vectorStep f m) := by
  apply integrable_finsetSum
  intro j hj
  exact (integrable_const _).indicator measurableSet_Ioc

lemma vectorStep_integral (μ : VectorMeasure unitInterval F) [IsFiniteMeasure μ.variation]
    [CompleteSpace G] (P : E →L[ℝ] F →L[ℝ] G) (f : unitInterval → E) (m : ℕ) :
    μ.integral (vectorStep f m) P = ∑j∈Finset.range m,
      P (f (unitGrid m j)) (μ (Ioc (unitGrid m j) (unitGrid m (j+1)))) := by
  unfold vectorStep
  rw [VectorMeasure.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact VectorMeasure.integral_indicator_const _ measurableSet_Ioc
  · intro j hj
    exact (integrable_const _).indicator measurableSet_Ioc

omit [NormedSpace ℝ E] in
lemma vectorStep_tendsto (f : unitInterval → E) (hf : Continuous f)
    (t : unitInterval) (ht : t≠0) : Tendsto (fun n : ℕ => vectorStep f (n+1) t) atTop (nhds (f t)) := by
  have huc := isCompact_univ.uniformContinuousOn_of_continuous hf.continuousOn
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδf⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  have hevent : ∀ᶠ n : ℕ in atTop,(1:ℝ)/((n+1:ℕ):ℝ)<δ := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually (gt_mem_nhds hδ)
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  filter_upwards [hevent] with n hn
  obtain ⟨j,hj,htj⟩ := exists_grid_cell (n+1) (Nat.succ_pos _) t ht
  rw [vectorStep_eq_cell f (n+1) j (Nat.succ_pos _) hj t htj]
  apply hδf _ (mem_univ _) _ (mem_univ _)
  rw [dist_comm]
  exact (grid_cell_dist (n+1) j (Nat.succ_pos _) hj t htj).trans_lt hn

omit [NormedSpace ℝ E] in
lemma vectorStep_bound (f : unitInterval → E) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀t,‖f t‖ ≤ C) (m : ℕ) (hm : 0 < m) (t : unitInterval) : ‖vectorStep f m t‖ ≤ C := by
  by_cases ht : t=0
  · subst t;simpa only [vectorStep_zero,norm_zero] using hC
  · obtain ⟨j,hj,htj⟩ := exists_grid_cell m hm t ht
    rw [vectorStep_eq_cell f m j hm hj t htj]
    exact hf _

theorem tendsto_vectorStep_integral (μ : VectorMeasure unitInterval F) [IsFiniteMeasure μ.variation]
    (hμ₀ : μ ({0}:Set unitInterval)=0) (P : E →L[ℝ] F →L[ℝ] G)
    (f : unitInterval → E) (hf : Continuous f) :
    Tendsto (fun n : ℕ => μ.integral (vectorStep f (n+1)) P) atTop (nhds (μ.integral f P)) := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hC₀ : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0 (mem_univ _))
  have hμv₀ := variation_singleton_zero μ 0 hμ₀
  have hae : ∀ᵐt∂μ.variation,t≠0 := by simpa only [ae_iff,not_not,Set.ofPred_eq_eq_singleton] using hμv₀
  apply VectorMeasure.tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall fun n => (vectorStep_integrable μ f (n+1)).aestronglyMeasurable
  · refine ⟨C,Eventually.of_forall fun n => ?_⟩
    exact Eventually.of_forall fun t => vectorStep_bound f C hC₀ (fun t => hC t (mem_univ _)) (n+1) (Nat.succ_pos _) t
  · filter_upwards [hae] with t ht
    exact vectorStep_tendsto f hf t ht

end ConvexSkorokhod

end OAI
