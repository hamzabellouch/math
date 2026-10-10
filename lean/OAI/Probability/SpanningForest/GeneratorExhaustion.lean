import Mathlib

namespace OAI

noncomputable section

open Filter Topology

namespace Problem336
namespace FreeKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def finiteSpan {α : Type*} (v : α → E) (s : Finset α) : Submodule ℝ E :=
  Submodule.span ℝ (v '' (s : Set α))

instance finiteSpan_finiteDimensional {α : Type*} (v : α → E) (s : Finset α) :
    FiniteDimensional ℝ (finiteSpan v s) :=
  FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image v)

theorem finiteSpan_mono {α : Type*} (v : α → E) {s t : Finset α}
    (h : s ⊆ t) : finiteSpan v s ≤ finiteSpan v t :=
  Submodule.span_mono (Set.image_mono h)

theorem iSup_finiteSpan_eq_span_range {α : Type*} (v : α → E)
    (s : ℕ → Finset α) (hCover : ∀ a, ∃ n, a ∈ s n) :
    (⨆ n, finiteSpan v (s n)) = Submodule.span ℝ (Set.range v) := by
  apply le_antisymm
  · refine iSup_le fun n => Submodule.span_mono ?_
    exact Set.image_subset_range v (s n : Set α)
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    obtain ⟨n, hn⟩ := hCover a
    exact (le_iSup (fun n => finiteSpan v (s n)) n)
      (Submodule.subset_span ⟨a, hn, rfl⟩)

theorem finiteSpan_projection_tendsto_self {α : Type*} (v : α → E)
    (s : ℕ → Finset α) (hMono : Monotone s)
    (hCover : ∀ a, ∃ n, a ∈ s n)
    (hDense : (Submodule.span ℝ (Set.range v)).topologicalClosure = ⊤)
    (x : E) :
    Tendsto (fun n => (finiteSpan v (s n)).starProjection x) atTop (𝓝 x) := by
  apply Submodule.starProjection_tendsto_self
  · intro n m hnm
    exact finiteSpan_mono v (hMono hnm)
  · rw [iSup_finiteSpan_eq_span_range v s hCover, hDense]

theorem exhausted_generators_minor_tendsto
    [CompleteSpace E]
    {α β ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : α → E) (c : β → E)
    (s : ℕ → Finset α) (t : ℕ → Finset β)
    (hs : Monotone s) (ht : Monotone t)
    (hsCover : ∀ a, ∃ n, a ∈ s n)
    (htCover : ∀ b, ∃ n, b ∈ t n)
    (hqDense : (Submodule.span ℝ (Set.range q)).topologicalClosure = ⊤)
    (v : ι → E) :
    Tendsto
      (fun n => Matrix.det (fun i j => inner ℝ (v i)
        ((finiteSpan q (s n)).starProjection (v j) -
          (finiteSpan c (t n)).starProjection (v j))))
      atTop
      (𝓝 (Matrix.det (fun i j => inner ℝ (v i)
        (v j - (Submodule.span ℝ (Set.range c)).topologicalClosure.starProjection
          (v j))))) := by
  have hQ : Monotone (fun n => finiteSpan q (s n)) :=
    fun _ _ h => finiteSpan_mono q (hs h)
  have hC : Monotone (fun n => finiteSpan c (t n)) :=
    fun _ _ h => finiteSpan_mono c (ht h)
  have hDense : (⨆ n, finiteSpan q (s n)).topologicalClosure = ⊤ := by
    rw [iSup_finiteSpan_eq_span_range q s hsCover, hqDense]
  have hp : ∀ x, Tendsto
      (fun n => (finiteSpan q (s n)).starProjection x -
        (finiteSpan c (t n)).starProjection x) atTop
      (𝓝 (x - (Submodule.span ℝ (Set.range c)).topologicalClosure.starProjection x)) := by
    intro x
    have hc := Submodule.starProjection_tendsto_closure_iSup
      (fun n => finiteSpan c (t n)) hC x
    rw [iSup_finiteSpan_eq_span_range c t htCover] at hc
    exact (finiteSpan_projection_tendsto_self q s hs hsCover hqDense x).sub hc
  have hm : Tendsto
      (fun n i j => inner ℝ (v i)
        ((finiteSpan q (s n)).starProjection (v j) -
          (finiteSpan c (t n)).starProjection (v j))) atTop
      (𝓝 (fun i j => inner ℝ (v i)
        (v j - (Submodule.span ℝ (Set.range c)).topologicalClosure.starProjection
          (v j)))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact tendsto_const_nhds.inner (hp (v j))
  exact continuous_id.matrix_det.continuousAt.tendsto.comp hm

end FreeKernel
end Problem336

end

end OAI
