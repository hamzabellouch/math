import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace OAI

/-! Nested compact cutoffs in finite-dimensional parameter spaces. -/
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.CollarVelocity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma compact_open_thickening {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ IsCompact (closure V) ∧ closure V ⊆ U := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V, hV, hKV, hVU⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter isOpen_ball).mem_nhdsSet.mpr (subset_inter hKU hr))
  refine ⟨V, hV, hKV, ?_, fun x hx => (hVU hx).1⟩
  exact (isCompact_closedBall (0 : E) r).of_isClosed_subset isClosed_closure
    (fun x hx => ball_subset_closedBall (hVU hx).2)

theorem compact_cutoff {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨V, hV, hKV, hVc, hVU⟩ := compact_open_thickening hK hU hKU
  obtain ⟨χ, hχ, hχr, hχs, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV hK.isClosed hKV
  have hs : tsupport χ = closure V := by
    change closure (Function.support χ) = closure V
    rw [hχs]
  refine ⟨χ, hχ, ?_, fun x => hχr (mem_range_self x), ?_, ?_⟩
  · change IsCompact (tsupport χ)
    rw [hs]
    exact hVc
  · rw [hs]
    exact hVU
  · exact fun x hx => (hχone x).mp hx

/-- The inner cutoff is one on an open collar, and the outer one is one
on the whole closed support of the inner cutoff. -/
theorem nested_compact_cutoffs {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      ∃ φ χ : E → ℝ, ContDiff ℝ ∞ φ ∧ ContDiff ℝ ∞ χ ∧
        HasCompactSupport φ ∧ HasCompactSupport χ ∧
        (∀ x, φ x ∈ Icc (0 : ℝ) 1) ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
        tsupport χ ⊆ U ∧ tsupport φ ⊆ U ∧
        (∀ x ∈ W, φ x = 1) ∧ (∀ x ∈ tsupport φ, χ x = 1) := by
  obtain ⟨V, hV, hKV, hVc, hVU⟩ := compact_open_thickening hK hU hKU
  obtain ⟨W, hW, hKW, hWc, hWV⟩ := compact_open_thickening hK hV hKV
  obtain ⟨φ, hφ, hφc, hφr, hφs, hφone⟩ := compact_cutoff hWc hV hWV
  obtain ⟨χ, hχ, hχc, hχr, hχs, hχone⟩ := compact_cutoff hVc hU hVU
  refine ⟨W, hW, hKW, ?_, φ, χ, hφ, hχ, hφc, hχc, hφr, hχr, hχs,
    hφs.trans (subset_closure.trans hVU), ?_, ?_⟩
  · exact subset_closure.trans (hWV.trans (subset_closure.trans hVU))
  · exact fun x hx => hφone x (subset_closure hx)
  · exact fun x hx => hχone x (subset_closure (hφs hx))

omit [FiniteDimensional ℝ E] in
lemma supported_local_mul {χ f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun x => χ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hn : x ∉ tsupport χ := fun h => hx (hs h)
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    exact (congrArg (fun t : ℝ => t * f y) hy).trans (zero_mul _)

omit [FiniteDimensional ℝ E] in
lemma supported_local_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : E → ℝ} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun x => χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
  · have hn : x ∉ tsupport χ := fun h => hx (hs h)
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    exact (congrArg (fun t : ℝ => t • f y) hy).trans (zero_smul ℝ _)

theorem compact_smooth_extension {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      ∃ g : E → F, ContDiff ℝ ∞ g ∧ EqOn g f W := by
  obtain ⟨W, hW, hKW, hWU, φ, χ, hφ, _, _, _, _, _, _, hφs, hφone, _⟩ :=
    nested_compact_cutoffs hK hU hKU
  exact ⟨W, hW, hKW, hWU, fun x => φ x • f x,
    supported_local_smul hU hφ hf hφs, fun x hx => by simp only [hφone x hx, one_smul]⟩

end ClosedSurfaceR4.CollarVelocity

end

end OAI
