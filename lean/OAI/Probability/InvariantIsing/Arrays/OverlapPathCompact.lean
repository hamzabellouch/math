import OAI.Probability.InvariantIsing.Core.Variational

namespace OAI

/-! Sequential L1 compactness of bounded monotone overlap paths. The
proof extracts the values on the rationals and discards only the
countable discontinuity set of the resulting monotone path. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

private def rationalLowerValues (f : ℚ → Icc (0 : ℝ) 1) (x : ℝ) : Set ℝ :=
  (fun q : ℚ => (f q : ℝ)) '' {q : ℚ | (q : ℝ) < x}

private lemma rationalLowerValues_nonempty (f : ℚ → Icc (0 : ℝ) 1) (x : ℝ) :
    (rationalLowerValues f x).Nonempty := by
  obtain ⟨q, hq⟩ := exists_rat_lt x
  exact ⟨f q, q, hq, rfl⟩

private lemma rationalLowerValues_bdd (f : ℚ → Icc (0 : ℝ) 1) (x : ℝ) :
    BddAbove (rationalLowerValues f x) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨q, _, rfl⟩
  exact (f q).property.2

private def rationalLowerPath (f : ℚ → Icc (0 : ℝ) 1) : OverlapPath where
  val x := sSup (rationalLowerValues f x)
  monotone := by
    intro x y hxy
    apply csSup_le_csSup (rationalLowerValues_bdd f y) (rationalLowerValues_nonempty f x)
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q, hq.trans_le hxy, rfl⟩
  nonneg x := by
    obtain ⟨q, hq⟩ := exists_rat_lt x
    exact (f q).property.1.trans (le_csSup (rationalLowerValues_bdd f x) ⟨q, hq, rfl⟩)
  le_one x := by
    apply csSup_le (rationalLowerValues_nonempty f x)
    rintro _ ⟨q, _, rfl⟩
    exact (f q).property.2

private lemma rational_le_lowerPath (f : ℚ → Icc (0 : ℝ) 1)
    {q : ℚ} {x : ℝ} (hq : (q : ℝ) < x) : (f q : ℝ) ≤ rationalLowerPath f x :=
  le_csSup (rationalLowerValues_bdd f x) ⟨q, hq, rfl⟩

private lemma rationalLowerPath_tendsto (p : ℕ → OverlapPath)
    (f : ℚ → Icc (0 : ℝ) 1)
    (hf : ∀ q : ℚ, Tendsto (fun n => p n (q : ℝ)) atTop (𝓝 (f q : ℝ)))
    (x : ℝ) (hx : ContinuousAt (rationalLowerPath f) x) :
    Tendsto (fun n => p n x) atTop (𝓝 (rationalLowerPath f x)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨y, hy, hay⟩ := (lt_csSup_iff (rationalLowerValues_bdd f x)
      (rationalLowerValues_nonempty f x)).mp ha
    obtain ⟨q, hqx, rfl⟩ := hy
    filter_upwards [(hf q).eventually (Ioi_mem_nhds hay)] with n hn
    exact hn.trans_le ((p n).monotone hqx.le)
  · intro b hb
    have hnear : {y : ℝ | rationalLowerPath f y < b} ∈ 𝓝 x :=
      hx (Iio_mem_nhds hb)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
    let y := x + ε / 2
    have hxy : x < y := by dsimp [y]; linarith
    have hy : rationalLowerPath f y < b := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hxy)]
      dsimp [y]
      linarith
    obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hxy
    have hqb : (f q : ℝ) < b := (rational_le_lowerPath f hqy).trans_lt hy
    filter_upwards [(hf q).eventually (Iio_mem_nhds hqb)] with n hn
    exact ((p n).monotone hxq.le).trans_lt hn

/-- Every sequence of overlap quantiles has an L1-convergent subsequence
with another admissible bounded monotone representative. -/
theorem overlapPath_ae_l1_subsequence (p : ℕ → OverlapPath) :
    ∃ q : OverlapPath, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ᵐ s ∂pathMeasure, Tendsto (fun n => p (φ n) s) atTop (𝓝 (q s))) ∧
      Tendsto (fun n => ∫ s, |p (φ n) s - q s| ∂pathMeasure) atTop (𝓝 0) := by
  let f : ℕ → ℚ → Icc (0 : ℝ) 1 := fun n r => ⟨p n r, (p n).nonneg r, (p n).le_one r⟩
  obtain ⟨g, φ, hφ, hg⟩ := CompactSpace.tendsto_subseq f
  let q := rationalLowerPath g
  have hr (r : ℚ) : Tendsto (fun n => p (φ n) (r : ℝ)) atTop (𝓝 (g r : ℝ)) :=
    (continuous_subtype_val.tendsto (g r)).comp ((continuous_apply r).tendsto g |>.comp hg)
  have hc : ∀ᵐ s ∂pathMeasure, ContinuousAt q s := by
    let : NullSingletonClass pathMeasure := by unfold pathMeasure; infer_instance
    have hz := q.monotone.countable_not_continuousAt.measure_zero (μ := pathMeasure)
    have hae : ∀ᵐ s ∂pathMeasure, s ∉ {x | ¬ContinuousAt q x} := compl_mem_ae_iff.mpr hz
    filter_upwards [hae] with s hs
    exact not_not.mp hs
  have hpoint : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => p (φ n) s) atTop (𝓝 (q s)) := by
    filter_upwards [hc] with s hs
    exact rationalLowerPath_tendsto (fun n => p (φ n)) g hr s hs
  refine ⟨q, φ, hφ, hpoint, ?_⟩
  have ht := tendsto_integral_of_dominated_convergence (μ := pathMeasure)
    (F := fun n s => |p (φ n) s - q s|) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun n => ((p (φ n)).measurable.sub q.measurable).abs.aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_le.mpr ⟨by linarith [(p (φ n)).nonneg s, q.le_one s],
        by linarith [(p (φ n)).le_one s, q.nonneg s]⟩) (by
      filter_upwards [hpoint] with s hs
      simpa only [sub_self, abs_zero] using (hs.sub_const (q s)).abs)
  simpa only [integral_zero] using ht

theorem overlapPath_l1_subsequence (p : ℕ → OverlapPath) :
    ∃ q : OverlapPath, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => ∫ s, |p (φ n) s - q s| ∂pathMeasure) atTop (𝓝 0) := by
  obtain ⟨q, φ, hφ, _, hq⟩ := overlapPath_ae_l1_subsequence p
  exact ⟨q, φ, hφ, hq⟩

end InvariantIsing

end

end OAI
