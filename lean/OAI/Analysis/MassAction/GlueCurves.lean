import Mathlib

namespace OAI

universe uIota uE

noncomputable section

open scoped Topology

namespace Problem326

/-- Compatible differentiable curves on an open cover glue to one curve.
 The vector field may depend on time, and ordinary two-sided derivatives
 are preserved at all points. -/
theorem glue_hasDerivAt_of_open_cover {ι : Type uIota} {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : ι → Set ℝ) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ t, ∃ i, t ∈ U i) (curve : ι → ℝ → E)
    (hcompat : ∀ i j, Set.EqOn (curve i) (curve j) (U i ∩ U j))
    (v : ℝ → E → E)
    (hderiv : ∀ i t, t ∈ U i → HasDerivAt (curve i) (v t (curve i t)) t) :
    ∃ x : ℝ → E, (∀ i, Set.EqOn x (curve i) (U i)) ∧
      ∀ t, HasDerivAt x (v t (x t)) t := by
  choose index hindex using hcover
  let x : ℝ → E := fun t => curve (index t) t
  have hx : ∀ i, Set.EqOn x (curve i) (U i) := by
    intro i t ht
    exact hcompat (index t) i ⟨hindex t, ht⟩
  refine ⟨x, hx, ?_⟩
  intro t
  let i := index t
  have ht : t ∈ U i := hindex t
  have heq : x =ᶠ[𝓝 t] curve i :=
    (show ∀ᶠ s in 𝓝 t, s ∈ U i from (hopen i).mem_nhds ht).mono
      (fun s hs => hx i hs)
  rw [hx i ht]
  exact (hderiv i t ht).congr_of_eventuallyEq heq

/-- A family on expanding symmetric intervals is an open cover of real time. -/
theorem symmetric_intervals_cover (t : ℝ) :
    ∃ n : ℕ, t ∈ Set.Ioo (-(n : ℝ) - 1) ((n : ℝ) + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt |t|
  refine ⟨n, ?_, ?_⟩
  · have := neg_abs_le t
    linarith
  · have := le_abs_self t
    linarith

/-- The countable-interval specialization used to globalize finite-horizon ODE
 solutions without losing differentiability at time zero. -/
theorem glue_hasDerivAt_on_symmetric_intervals {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (curve : ℕ → ℝ → E) (v : ℝ → E → E)
    (hcompat : ∀ m n, Set.EqOn (curve m) (curve n)
      (Set.Ioo (-(m : ℝ) - 1) ((m : ℝ) + 1) ∩
       Set.Ioo (-(n : ℝ) - 1) ((n : ℝ) + 1)))
    (hderiv : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Ioo (-(n : ℝ) - 1) ((n : ℝ) + 1) →
      HasDerivAt (curve n) (v t (curve n t)) t) :
    ∃ x : ℝ → E,
      (∀ n, Set.EqOn x (curve n) (Set.Ioo (-(n : ℝ) - 1) ((n : ℝ) + 1))) ∧
      ∀ t, HasDerivAt x (v t (x t)) t :=
  glue_hasDerivAt_of_open_cover _ (fun _ => isOpen_Ioo)
    symmetric_intervals_cover curve hcompat v hderiv

end Problem326

end

end OAI
