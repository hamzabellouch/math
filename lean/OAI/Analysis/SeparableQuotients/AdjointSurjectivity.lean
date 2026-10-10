import OAI.Analysis.SeparableQuotients.QuotientPerturbation

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped Topology

universe u v

section RealAdjoint
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Hahn–Banach ball inclusion with a quantitative lower bound. -/
theorem ball_image_closure_of_adjoint_bound
    (T : E →L[ℝ] F) (c : ℝ) (_hc : 0 < c)
    (hT : ∀ g : StrongDual ℝ F, c * ‖g‖ ≤ ‖g.comp T‖) :
    closedBall (0 : F) c ⊆ closure (T '' closedBall (0 : E) 1) := by
  intro y hy
  simp only [mem_closedBall, dist_zero_right] at hy
  by_contra hn
  have hconv : Convex ℝ (closure (T '' closedBall (0 : E) 1)) :=
    ((convex_closedBall (0 : E) 1).linear_image T.toLinearMap).closure
  obtain ⟨g, a, hga, hay⟩ := geometric_hahn_banach_closed_point hconv isClosed_closure hn
  have ha : 0 < a := by
    have := hga (T 0) (subset_closure ⟨0, by simp, rfl⟩)
    simpa using this
  have hnorm : ‖g.comp T‖ ≤ a := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm ha.le
    intro x hx
    have hx' : x ∈ closedBall (0 : E) 1 := by simp [mem_closedBall, hx]
    have hnx' : -x ∈ closedBall (0 : E) 1 := by simp [mem_closedBall, hx]
    have hp := hga (T x) (subset_closure ⟨x, hx', rfl⟩)
    have hm := hga (T (-x)) (subset_closure ⟨-x, hnx', rfl⟩)
    simp only [map_neg] at hm
    change |g (T x)| ≤ a
    exact abs_le.mpr ⟨by linarith, hp.le⟩
  have hgy : g y ≤ ‖g‖ * c :=
    (le_abs_self _).trans ((g.le_opNorm y).trans
      (mul_le_mul_of_nonneg_left hy (norm_nonneg g)))
  have hb := hT g
  nlinarith

/-- Approximate lifting with a quantitative norm bound. -/
theorem approximate_lift_of_adjoint_bound
    (T : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hT : ∀ g : StrongDual ℝ F, c * ‖g‖ ≤ ‖g.comp T‖) (y : F) :
    ∃ x : E, ‖y - T x‖ ≤ (1 / 2 : ℝ) * ‖y‖ ∧ ‖x‖ ≤ c⁻¹ * ‖y‖ := by
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp, by simp⟩
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hmem : (c / ‖y‖) • y ∈ closedBall (0 : F) c := by
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hc hn)]
    exact le_of_eq (div_mul_cancel₀ c (ne_of_gt hn))
  have hcl := ball_image_closure_of_adjoint_bound T c hc hT hmem
  obtain ⟨w, ⟨z, hz, rfl⟩, hw⟩ := Metric.mem_closure_iff.mp hcl (c / 2) (by positivity)
  refine ⟨(‖y‖ / c) • z, ?_, ?_⟩
  · have heq : y - T ((‖y‖ / c) • z) =
        (‖y‖ / c) • ((c / ‖y‖) • y - T z) := by
      rw [smul_sub, smul_smul, map_smul]
      have : ‖y‖ / c * (c / ‖y‖) = 1 := by field_simp
      rw [this, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hn hc)]
    rw [dist_eq_norm] at hw
    calc
      ‖y‖ / c * ‖(c / ‖y‖) • y - T z‖ ≤ ‖y‖ / c * (c / 2) :=
        mul_le_mul_of_nonneg_left hw.le (div_pos hn hc).le
      _ = (1 / 2 : ℝ) * ‖y‖ := by field_simp
  · simp only [mem_closedBall, dist_zero_right] at hz
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hn hc)]
    calc
      ‖y‖ / c * ‖z‖ ≤ ‖y‖ / c * 1 := mul_le_mul_of_nonneg_left hz (div_pos hn hc).le
      _ = c⁻¹ * ‖y‖ := by ring

/-- The elementary completion argument, with no open-mapping assumption. -/
theorem exact_lift_of_approximate [CompleteSpace E]
    (T : E →L[ℝ] F) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ y : F, ∃ x : E, ‖y - T x‖ ≤ (1 / 2 : ℝ) * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖)
    (y : F) : ∃ x : E, T x = y ∧ ‖x‖ ≤ 2 * C * ‖y‖ := by
  classical
  choose g hg using ha
  let h (z : F) := z - T (g z)
  have hle : ∀ z, ‖h z‖ ≤ (1 / 2 : ℝ) * ‖z‖ := fun z => (hg z).1
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2 : ℝ) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ']
      apply (hle _).trans
      rw [pow_succ', mul_assoc]
      gcongr
  let u (n : ℕ) := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2 : ℝ) ^ n * (C * ‖y‖) := by
    intro n
    apply (hg _).2.trans
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2 : ℝ) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2 : ℝ) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable (fun n => ‖u n‖) := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ summable_geometric_two
  have su : Summable u := sNu.of_norm
  have xineq : ‖∑' n, u n‖ ≤ 2 * C * ‖y‖ := by
    calc
      ‖∑' n, u n‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2 : ℝ) ^ n * (C * ‖y‖) :=
        sNu.tsum_le_tsum ule (Summable.mul_right _ summable_geometric_two)
      _ = (∑' n, (1 / 2 : ℝ) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
  have fsumeq : ∀ n : ℕ, T (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, T.map_add, ih, Function.iterate_succ_apply', sub_add]
  have L₁ : Filter.Tendsto (fun n => T (∑ i ∈ Finset.range n, u i))
      Filter.atTop (𝓝 (T (∑' n, u n))) :=
    (T.continuous.tendsto _).comp su.hasSum.tendsto_sum_nat
  simp only [fsumeq] at L₁
  have L₂ : Filter.Tendsto (fun n => y - h^[n] y) Filter.atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul tendsto_const_nhds
  exact ⟨∑' n, u n, by simpa using tendsto_nhds_unique L₁ L₂, xineq⟩

/-- Adjoint lower bounds force surjectivity. -/
theorem surjective_of_adjoint_bound [CompleteSpace E]
    (T : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hT : ∀ g : StrongDual ℝ F, c * ‖g‖ ≤ ‖g.comp T‖) :
    Function.Surjective T := by
  intro y
  obtain ⟨x, hx, _⟩ := exact_lift_of_approximate T c⁻¹ (inv_nonneg.mpr hc.le)
    (approximate_lift_of_adjoint_bound T c hc hT) y
  exact ⟨x, hx⟩

end RealAdjoint
section RCLikeAdjoint
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The surjectivity test over either original scalar field. -/
theorem surjective_of_adjoint_bound_rclike
    (T : E →L[𝕜] F) (c : ℝ) (hc : 0 < c)
    (hT : ∀ g : StrongDual 𝕜 F, c * ‖g‖ ≤ ‖g.comp T‖) :
    Function.Surjective T := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F
  have hb : ∀ g : StrongDual ℝ F, c * ‖g‖ ≤ ‖g.comp (T.restrictScalars ℝ)‖ := by
    intro g
    have heq : StrongDual.extendRCLike (g.comp (T.restrictScalars ℝ)) =
        (g.extendRCLike : StrongDual 𝕜 F).comp T := by
      ext x
      simp [StrongDual.extendRCLike_apply]
    have h := hT g.extendRCLike
    rw [StrongDual.norm_extendRCLike, ← heq, StrongDual.norm_extendRCLike] at h
    exact h
  exact surjective_of_adjoint_bound (T.restrictScalars ℝ) c hc hb

end RCLikeAdjoint
end SeparableQuotient

end OAI
