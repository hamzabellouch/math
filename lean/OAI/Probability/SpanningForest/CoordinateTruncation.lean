import Mathlib

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology ENNReal

namespace Problem336.CoordinateTruncation

variable {ι 𝕜 : Type*} [DecidableEq ι] [RCLike 𝕜]

abbrev Space (ι 𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ι => 𝕜) 2

def truncate (s : Finset ι) : Space ι 𝕜 →L[𝕜] Space ι 𝕜 :=
  ∑ i ∈ s, (lp.singleContinuousLinearMap 𝕜 (fun _ : ι => 𝕜) 2 i).comp
    (lp.evalCLM 𝕜 (fun _ : ι => 𝕜) 2 i)

lemma truncate_eq_sum (s : Finset ι) (x : Space ι 𝕜) :
    truncate s x = ∑ i ∈ s, lp.single 2 i (x i) := by
  simp only [truncate, sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rfl

@[simp] theorem truncate_apply (s : Finset ι) (x : Space ι 𝕜) (i : ι) :
    truncate s x i = if i ∈ s then x i else 0 := by
  rw [truncate_eq_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single]

theorem tendsto_truncate (s : ℕ → Finset ι) (hmono : Monotone s)
    (hcover : ∀ i, ∃ n, i ∈ s n) (x : Space ι 𝕜) :
    Tendsto (fun n => truncate (s n) x) atTop (𝓝 x) := by
  simpa only [truncate_eq_sum, Function.comp_def] using
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x).comp
      (hmono.tendsto_atTop_finset hcover)

def supported (s : Set ι) : Submodule 𝕜 (Space ι 𝕜) where
  carrier := {x | ∀ i, i ∉ s → x i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
  smul_mem' := by intro c x hx i hi; simp [hx i hi]

omit [DecidableEq ι] in
@[simp] theorem mem_supported (s : Set ι) (x : Space ι 𝕜) :
    x ∈ supported s ↔ ∀ i, i ∉ s → x i = 0 := Iff.rfl

omit [DecidableEq ι] in
theorem supported_mono {s t : Set ι} (h : s ⊆ t) :
    supported (𝕜 := 𝕜) s ≤ supported t := by
  intro x hx i hi
  exact hx i (fun hs => hi (h hs))

instance supported_isClosed (s : Set ι) :
    IsClosed (supported (𝕜 := 𝕜) s : Set (Space ι 𝕜)) := by
  change IsClosed {x : Space ι 𝕜 | ∀ i, i ∉ s → x i = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro hi
  exact isClosed_eq ((continuous_apply i).comp lp.uniformContinuous_coe.continuous)
    continuous_const

instance supported_completeSpace (s : Set ι) :
    CompleteSpace (supported (𝕜 := 𝕜) s) := IsClosed.completeSpace_coe

instance supported_hasOrthogonalProjection (s : Set ι) :
    (supported (𝕜 := 𝕜) s).HasOrthogonalProjection := inferInstance

theorem single_mem_supported {s : Set ι} {i : ι} (hi : i ∈ s) (a : 𝕜) :
    lp.single 2 i a ∈ supported s := by
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact hj hi
  simp [lp.single_apply, Pi.single_eq_of_ne hji]

theorem supported_starProjection_apply (s : Set ι) [DecidablePred (· ∈ s)] (x : Space ι 𝕜) (i : ι) :
    (supported s).starProjection x i = if i ∈ s then x i else 0 := by
  classical
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi]
    have ho := (supported s).sub_starProjection_mem_orthogonal x
      (lp.single 2 i (1 : 𝕜)) (single_mem_supported hi 1)
    rw [lp.inner_single_left] at ho
    simpa using (sub_eq_zero.mp (by simpa using ho) :
      x i = (supported s).starProjection x i).symm
  · rw [ite_eq_right hi]
    exact (supported s).starProjection_apply_mem x i hi

theorem truncate_mem_supported (s : Finset ι) (x : Space ι 𝕜) :
    truncate s x ∈ supported (s : Set ι) := by
  intro i hi
  simp only [Finset.mem_coe] at hi
  simp [hi]

theorem sub_truncate_mem_orthogonal (s : Finset ι) (x : Space ι 𝕜) :
    x - truncate s x ∈ (supported (s : Set ι))ᗮ := by
  intro y hy
  rw [lp.inner_eq_tsum]
  have hz : ∀ i, inner 𝕜 (y i) ((x - truncate s x) i) = 0 := by
    intro i
    by_cases hi : i ∈ s
    · simp [hi]
    · have hyi : y i = 0 := hy i hi
      simp [hyi]
  simp only [hz, tsum_zero]

theorem starProjection_supported (s : Finset ι) :
    (supported (𝕜 := 𝕜) (s : Set ι)).starProjection = truncate s := by
  apply ContinuousLinearMap.ext
  intro x
  exact Submodule.eq_starProjection_of_mem_orthogonal
    (truncate_mem_supported s x) (sub_truncate_mem_orthogonal s x)

theorem closure_iSup_supported (s : ℕ → Finset ι) (S : Set ι)
    (hcover : ∀ i, i ∈ S ↔ ∃ n, i ∈ s n) :
    (⨆ n, supported (𝕜 := 𝕜) (s n : Set ι)).topologicalClosure = supported S := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro n
      apply supported_mono
      intro i hi
      exact (hcover i).mpr ⟨n, hi⟩
    · exact supported_isClosed S
  · intro x hx
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    apply mem_closure_of_tendsto
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
    apply Eventually.of_forall
    intro t
    apply Submodule.sum_mem
    intro i hi
    by_cases his : i ∈ S
    · obtain ⟨n, hin⟩ := (hcover i).mp his
      exact Submodule.mem_iSup_of_mem n (single_mem_supported hin (x i))
    · simp only [hx i his, lp.single_zero]
      exact Submodule.zero_mem _

theorem tendsto_truncate_supported (s : ℕ → Finset ι) (hmono : Monotone s)
    (S : Set ι) (hcover : ∀ i, i ∈ S ↔ ∃ n, i ∈ s n) (x : Space ι 𝕜) :
    Tendsto (fun n => truncate (s n) x) atTop
      (𝓝 ((supported S).starProjection x)) := by
  have h := Submodule.starProjection_tendsto_closure_iSup
    (fun n => supported (𝕜 := 𝕜) (s n : Set ι))
    (fun m n hmn => supported_mono (hmono hmn)) x
  simpa only [starProjection_supported, closure_iSup_supported s S hcover] using h

end Problem336.CoordinateTruncation

end

end OAI
