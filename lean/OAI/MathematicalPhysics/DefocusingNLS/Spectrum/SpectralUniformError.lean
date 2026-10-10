import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Field.Basic

namespace OAI

/-! A scalar error sequence for uniformly converging bounded coefficients. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralUniform_error_bound {s : Set ℝ} (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : TendstoUniformlyOn f g atTop s)
    (hb : ∀ n, ∃ B : ℝ, ∀ r ∈ s, ‖f n r-g r‖ ≤ B) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ n r, r ∈ s → ‖f n r-g r‖ ≤ δ n := by
  let A := fun n => insert (0 : ℝ) ((fun r => ‖f n r-g r‖) '' s)
  have hne (n : ℕ) : (A n).Nonempty := ⟨0,mem_insert _ _⟩
  have hbd (n : ℕ) : BddAbove (A n) := by
    obtain ⟨B,hB⟩ := hb n
    refine ⟨max 0 B,?_⟩
    rintro y (rfl | ⟨r,hr,rfl⟩)
    · exact le_max_left _ _
    · exact (hB r hr).trans (le_max_right _ _)
  let δ := fun n => sSup (A n)
  have hδ (n : ℕ) : 0 ≤ δ n := le_csSup (hbd n) (mem_insert _ _)
  refine ⟨δ,hδ,?_,fun n r hr => le_csSup (hbd n) (mem_insert_of_mem _ ⟨r,hr,rfl⟩)⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hf) (ε/2) (half_pos hε)] with n hn
  have he : δ n ≤ ε/2 := by
    apply csSup_le (hne n)
    rintro y (rfl | ⟨r,hr,rfl⟩)
    · exact (half_pos hε).le
    · have hh : ‖f n r-g r‖ < ε/2 := by
        simpa only [dist_eq_norm,norm_sub_rev] using hn r hr
      exact hh.le
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (hδ n)] using
    he.trans_lt (half_lt_self hε)

end DefocusingNLS

end OAI
