import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Pointwise convergence of operators with finite-dimensional domain -/

open Filter Topology

namespace DefocusingNLS

theorem tendsto_finite_domain_operator_of_basis {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Fintype ι] (b : Module.Basis ι ℝ E)
    (A : ℕ → E →L[ℝ] F) (B : E →L[ℝ] F)
    (h : ∀ i, Tendsto (fun n => A n (b i)) atTop (𝓝 (B (b i)))) :
    Tendsto A atTop (𝓝 B) := by
  classical
  obtain ⟨C, hC, hbound⟩ := b.exists_opNorm_le (F := F)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply (tendsto_order.2 ⟨?_, ?_⟩)
  · intro ε hε
    exact Filter.Eventually.of_forall (fun n => hε.trans_le (norm_nonneg _))
  · intro ε hε
    have he : 0 < ε / (2 * C) := div_pos hε (by positivity)
    have hh : ∀ᶠ n in atTop, ∀ i, ‖A n (b i) - B (b i)‖ < ε / (2 * C) := by
      apply eventually_all.mpr
      intro i
      exact (tendsto_iff_norm_sub_tendsto_zero.mp (h i)).eventually
        (eventually_lt_nhds he)
    filter_upwards [hh] with n hn
    have hb : ‖A n - B‖ ≤ C * (ε / (2 * C)) :=
      hbound he.le (fun i => (hn i).le)
    have hc : C * (ε / (2 * C)) = ε / 2 := by field_simp
    linarith

theorem tendsto_finite_domain_operator {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℕ → E →L[ℝ] F) (B : E →L[ℝ] F)
    (h : ∀ v, Tendsto (fun n => A n v) atTop (𝓝 (B v))) :
    Tendsto A atTop (𝓝 B) :=
  tendsto_finite_domain_operator_of_basis (Module.finBasis ℝ E) A B
    (fun i => h ((Module.finBasis ℝ E) i))

end DefocusingNLS

end OAI
