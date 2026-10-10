import Mathlib

namespace OAI

universe uE

noncomputable section

open Set Metric

namespace Problem326

/-- A continuously differentiable autonomous vector field admits a solution on a
closed interval of positive length, with ordinary derivatives at both endpoints. -/
theorem exists_local_solution_of_contDiffAt
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {z : E} (hf : ContDiffAt ℝ 1 f z) (t₀ : ℝ) :
    ∃ T : ℝ, 0 < T ∧ ∃ x : ℝ → E, x t₀ = z ∧
      ∀ t ∈ Icc (t₀ - T) (t₀ + T), HasDerivAt x (f (x t)) t := by
  obtain ⟨x, hx, ε, hε, hderiv⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  refine ⟨ε / 2, half_pos hε, x, hx, ?_⟩
  intro t ht
  apply hderiv t
  constructor <;> linarith [ht.1, ht.2]

/-- The local existence time can be chosen uniformly over a compact set of
initial states. This supplies fixed-size steps for compact trapping arguments. -/
theorem exists_uniform_local_solution_on_compact
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} (hf : ContDiff ℝ 1 f) {K : Set E} (hK : IsCompact K)
    (t₀ : ℝ) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∃ x : ℝ → E, x t₀ = z ∧
      ∀ t ∈ Icc (t₀ - T) (t₀ + T), HasDerivAt x (f (x t)) t := by
  classical
  have hlocal := fun z : E =>
    (hf.contDiffAt (x := z)).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt t₀
  choose r hr ε hε hsol using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun z => ball z (r z))
    (fun _ => isOpen_ball) (fun z _ => mem_iUnion.mpr ⟨z, mem_ball_self (hr z)⟩)
  let s' := insert (0 : E) s
  have hs' : s'.Nonempty := Finset.insert_nonempty _ _
  let T : ℝ := s'.inf' hs' (fun z => ε z / 2)
  have hT : 0 < T := by
    dsimp [T]
    exact (Finset.lt_inf'_iff hs').mpr (fun z _ => half_pos (hε z))
  refine ⟨T, hT, ?_⟩
  intro z hz
  obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hs hz)
  obtain ⟨x, hx, hderiv⟩ := hsol w z (ball_subset_closedBall hzw)
  have hTw : T ≤ ε w / 2 := Finset.inf'_le _ (Finset.mem_insert_of_mem hw)
  refine ⟨x, hx, ?_⟩
  intro t ht
  apply hderiv t
  constructor <;> linarith [ht.1, ht.2, hε w]

end Problem326

end

end OAI
