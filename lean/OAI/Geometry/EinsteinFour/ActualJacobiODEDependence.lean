import OAI.Geometry.EinsteinFour.ActualJacobiODEMatrix

namespace OAI

/-! Uniqueness and continuous parameter dependence for the bounded linear
equation used by the actual Jacobi fields. -/

namespace PositiveEinsteinFour.Jacobi

open Set Filter Metric
open scoped Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem global_linear_solution_unique (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) {γ η : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (A t (γ t)) t)
    (hη : ∀ t, HasDerivAt η (A t (η t)) t) (h0 : γ 0 = η 0) : γ = η := by
  funext t
  let r := |t| + 1
  have hr : 0 < r := by dsimp [r]; positivity
  exact linear_curve_eqOn_interval A K hK (fun s _ => hγ s) (fun s _ => hη s)
    (t := 0) ⟨by linarith, hr⟩ h0 (abs_lt.mp (lt_add_one |t|))

/-- A perturbation estimate uses a bound only on the reference solution. -/
theorem linear_solution_difference_bound (A B : ℝ → E →L[ℝ] E)
    (γ η : ℝ → E) (K : ℝ≥0) (δ C T : ℝ) (hδ : 0 ≤ δ)
    (hK : ∀ t, ‖A t‖ ≤ K)
    (hγ : ∀ t, HasDerivAt γ (A t (γ t)) t)
    (hη : ∀ t, HasDerivAt η (B t (η t)) t) (h0 : γ 0 = η 0)
    (hAB : ∀ s ∈ Icc 0 T, ‖A s - B s‖ ≤ δ)
    (hC : ∀ s ∈ Icc 0 T, ‖η s‖ ≤ C) :
    ∀ t ∈ Icc 0 T, ‖γ t - η t‖ ≤ gronwallBound 0 K (δ * C) t := by
  have hd (s : ℝ) : HasDerivAt (fun t => γ t - η t)
      (A s (γ s) - B s (η s)) s := (hγ s).sub (hη s)
  have hc : ContinuousOn (fun t => γ t - η t) (Icc 0 T) :=
    fun s _ => (hd s).continuousAt.continuousWithinAt
  have hb (s : ℝ) (hs : s ∈ Ico 0 T) :
      ‖A s (γ s) - B s (η s)‖ ≤ (K : ℝ) * ‖γ s - η s‖ + δ * C := by
    have heq : A s (γ s) - B s (η s) =
        A s (γ s - η s) + (A s - B s) (η s) := by
      simp only [map_sub, sub_apply]
      abel
    rw [heq]
    apply (norm_add_le _ _).trans
    apply add_le_add ((A s).le_of_opNorm_le (hK s) _)
    calc
      ‖(A s - B s) (η s)‖ ≤ δ * ‖η s‖ :=
        (A s - B s).le_of_opNorm_le (hAB s (Ico_subset_Icc_self hs)) _
      _ ≤ δ * C := mul_le_mul_of_nonneg_left (hC s (Ico_subset_Icc_self hs)) hδ
  intro t ht
  simpa only [sub_zero] using norm_le_gronwallBound_of_norm_deriv_right_le hc
    (fun s _ => (hd s).hasDerivWithinAt) (by rw [h0, sub_self, norm_zero]) hb t ht

theorem linear_solution_difference_bound_abs (A B : ℝ → E →L[ℝ] E)
    (γ η : ℝ → E) (K : ℝ≥0) (δ C T : ℝ) (hδ : 0 ≤ δ) (hC0 : 0 ≤ C)
    (hK : ∀ t, ‖A t‖ ≤ K)
    (hγ : ∀ t, HasDerivAt γ (A t (γ t)) t)
    (hη : ∀ t, HasDerivAt η (B t (η t)) t) (h0 : γ 0 = η 0)
    (hAB : ∀ s ∈ Icc (-T) T, ‖A s - B s‖ ≤ δ)
    (hC : ∀ s ∈ Icc (-T) T, ‖η s‖ ≤ C) (t : ℝ) (ht : |t| ≤ T) :
    ‖γ t - η t‖ ≤ gronwallBound 0 K (δ * C) T := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hmono := gronwallBound_mono (δ := 0) (K := (K : ℝ)) (ε := δ * C)
    le_rfl (mul_nonneg hδ hC0) K.coe_nonneg
  by_cases ht0 : 0 ≤ t
  · apply (linear_solution_difference_bound A B γ η K δ C T hδ hK hγ hη h0
      (fun s hs => hAB s ⟨by linarith [hs.1], hs.2⟩)
      (fun s hs => hC s ⟨by linarith [hs.1], hs.2⟩) t
      ⟨ht0, (le_abs_self t).trans ht⟩).trans
    exact hmono ((le_abs_self t).trans ht)
  · have hrevγ (s : ℝ) : HasDerivAt (fun u => γ (-u))
        ((-A (-s)) (γ (-s))) s := by
      simpa only [Function.comp_def, neg_one_smul, neg_apply] using
        (hγ (-s)).scomp s (hasDerivAt_id s).neg
    have hrevη (s : ℝ) : HasDerivAt (fun u => η (-u))
        ((-B (-s)) (η (-s))) s := by
      simpa only [Function.comp_def, neg_one_smul, neg_apply] using
        (hη (-s)).scomp s (hasDerivAt_id s).neg
    have habrev (s : ℝ) (hs : s ∈ Icc 0 T) : ‖-A (-s) - -B (-s)‖ ≤ δ := by
      simpa only [neg_sub_neg, norm_sub_rev] using hAB (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h := linear_solution_difference_bound (fun s => -A (-s)) (fun s => -B (-s))
      (fun s => γ (-s)) (fun s => η (-s)) K δ C T hδ
      (fun s => by simpa only [norm_neg] using hK (-s)) hrevγ hrevη
      (by simpa only [neg_zero] using h0) habrev
      (fun s hs => hC (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      (-t) ⟨by linarith, (neg_le_abs t).trans ht⟩
    simp only [neg_neg] at h
    exact h.trans (hmono ((neg_le_abs t).trans ht))

variable {P : Type*} [TopologicalSpace P]

theorem coefficient_eventually_close (A : ℝ × P → E →L[ℝ] E)
    (hA : Continuous A) (p : P) (T δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ q in 𝓝 p, ∀ s ∈ Icc (-T) T, ‖A (s, q) - A (s, p)‖ < δ := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro s _
  have hc : Continuous (fun q : P × ℝ => ‖A (q.2, q.1) - A (q.2, p)‖) :=
    (hA.comp (continuous_snd.prodMk continuous_fst)).sub
      (hA.comp (continuous_snd.prodMk continuous_const)) |>.norm
  exact hc.continuousAt.eventually (gt_mem_nhds (by simpa only [sub_self, norm_zero] using hδ))

/-- Continuity holds for any choice of the global solutions, since their
initial values are fixed and the bounded linear equation is unique. -/
theorem continuous_linear_solution_family (A : ℝ × P → E →L[ℝ] E)
    (γ : P → ℝ → E) (x : E) (hA : Continuous A) (K : ℝ≥0)
    (hK : ∀ s p, ‖A (s, p)‖ ≤ K) (h0 : ∀ p, γ p 0 = x)
    (hd : ∀ p s, HasDerivAt (γ p) (A (s, p) (γ p s)) s) :
    Continuous (fun p : ℝ × P => γ p.2 p.1) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t, p⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let T := |t| + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have hγc : Continuous (γ p) :=
    continuous_iff_continuousAt.mpr (fun s => (hd p s).continuousAt)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hγc.continuousOn
  let C₀ := max 0 C
  have hC0 : 0 ≤ C₀ := le_max_left _ _
  have hbound (s : ℝ) (hs : s ∈ Icc (-T) T) : ‖γ p s‖ ≤ C₀ :=
    (hC s hs).trans (le_max_right _ _)
  have hg : Tendsto (fun δ : ℝ => gronwallBound 0 K (δ * C₀) T) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, zero_mul, gronwallBound_ε0_δ0] using
      ((gronwallBound_continuous_ε 0 K T).comp (continuous_id.mul_const C₀)).tendsto 0
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hg (ε / 2) (half_pos hε))
  have hδsmall : gronwallBound 0 K ((δ / 2) * C₀) T < ε / 2 := by
    have hz := hsmall (show dist (δ / 2) 0 < δ by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; linarith)
    exact (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hz)
  have hcoeff := coefficient_eventually_close A hA p T (δ / 2) (half_pos hδ)
  have htime : ∀ᶠ u in 𝓝 t, |u| ≤ T := by
    exact (continuous_abs.tendsto t).eventually
      (eventually_le_nhds (show |t| < T by dsimp [T]; linarith))
  have hbase : ∀ᶠ u in 𝓝 t, dist (γ p u) (γ p t) < ε / 2 :=
    (hγc.tendsto t).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hcoeff,
    continuous_fst.continuousAt.preimage_mem_nhds htime,
    continuous_fst.continuousAt.preimage_mem_nhds hbase] with q hq hqt hqb
  have hdiff : ‖γ q.2 q.1 - γ p q.1‖ ≤ gronwallBound 0 K ((δ / 2) * C₀) T :=
    linear_solution_difference_bound_abs (fun s => A (s, q.2)) (fun s => A (s, p))
      (γ q.2) (γ p) K (δ / 2) C₀ T (half_pos hδ).le hC0
      (fun s => hK s q.2) (hd q.2) (hd p) ((h0 q.2).trans (h0 p).symm)
      (fun s hs => (hq s hs).le) hbound q.1 hqt
  apply (dist_triangle _ (γ p q.1) _).trans_lt
  calc
    dist (γ q.2 q.1) (γ p q.1) + dist (γ p q.1) (γ p t) < ε / 2 + ε / 2 :=
      add_lt_add (by simpa only [dist_eq_norm] using hdiff.trans_lt hδsmall) hqb
    _ = ε := add_halves ε

end
end PositiveEinsteinFour.Jacobi

end OAI
