import OAI.Analysis.CircleDomains.Probability.PathLawMixtures

namespace OAI

/-! Real-valued hit norms, their dual finite tests, and uniform strict inequalities
over compact configuration spaces. These are the topological estimates used in
the finite split of path-law fusion. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

section Paths

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem pathHitReal_upperSemicontinuous :
    UpperSemicontinuous (fun p : ProbabilityMeasure C(PathTime, X) × X =>
      pathHitReal p.1 p.2) := by
  intro p c hc
  have hfinite : pathHitProbability p.1 p.2 ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (pathHitProbability_le_one _ _) (by simp))
  have he := pathHitProbability_upperSemicontinuous p (ENNReal.ofReal c)
    ((ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr hc)
  exact he.mono fun _ h => ENNReal.toReal_lt_of_lt_ofReal h

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [BorelSpace C(PathTime, X)] in
theorem hasHitNormBound_iff_sum_sq_le
    (μ : ProbabilityMeasure C(PathTime, X)) {C : ℝ} (hC : 0 ≤ C) :
    HasHitNormBound μ C ↔ ∀ F : Finset X, ∑ x ∈ F, pathHitReal μ x ^ 2 ≤ C ^ 2 := by
  constructor
  · exact fun h => h.sum_sq_le
  · intro h F w _
    have hsqrt : Real.sqrt (∑ x ∈ F, pathHitReal μ x ^ 2) ≤ C :=
      (Real.sqrt_le_iff).mpr ⟨hC, h F⟩
    calc
      ∑ x ∈ F, w x * pathHitReal μ x ≤
          Real.sqrt (∑ x ∈ F, w x ^ 2) *
            Real.sqrt (∑ x ∈ F, pathHitReal μ x ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt (∑ x ∈ F, w x ^ 2) * C :=
        mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
      _ = _ := mul_comm _ _

end Paths

/-- For compact configurations, a joint upper semicontinuous strict bound persists
on an open set of centers. This is the neighborhood step of the finite split. -/
theorem isOpen_forall_compact_upper_bound {Z T : Type*}
    [TopologicalSpace Z] [TopologicalSpace T] [CompactSpace T]
    {f : Z × T → ℝ} (hf : UpperSemicontinuous f) (C : ℝ) :
    IsOpen {z | ∀ t, f (z, t) < C} := by
  have hc : IsClosed {p : Z × T | C ≤ f p} := hf.isClosed_preimage C
  have hp := isClosedMap_fst_of_compactSpace _ hc
  convert hp.isOpen_compl using 1
  ext z
  simp only [mem_compl_iff, mem_image, mem_ofPred_eq, Prod.exists, exists_and_right,
    exists_eq_right, not_exists, not_le]

theorem upperSemicontinuous_nonnegative_mul {Z : Type*} [TopologicalSpace Z]
    {f g : Z → ℝ} (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) :
    UpperSemicontinuous (fun z => f z * g z) := by
  intro z c hc
  have hcont : Continuous (fun δ : ℝ => (f z + δ) * (g z + δ)) := by fun_prop
  have he : ∀ᶠ δ : ℝ in 𝓝 0, (f z + δ) * (g z + δ) < c := by
    exact hcont.continuousAt.eventually (gt_mem_nhds (by simpa using hc))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  have hr2 : 0 < r / 2 := half_pos hr
  have hm : (f z + r / 2) * (g z + r / 2) < c :=
    hball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr2] using half_lt_self hr)
  filter_upwards [hf z (f z + r / 2) (by linarith),
    hg z (g z + r / 2) (by linarith)] with y hyf hyg
  exact lt_of_le_of_lt
    (mul_le_mul hyf.le hyg.le (hg0 y) (by linarith [hf0 z])) hm

end CircleDomainRigidity

end

end OAI
