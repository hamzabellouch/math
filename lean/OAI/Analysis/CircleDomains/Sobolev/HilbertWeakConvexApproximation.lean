import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Weak convergence gives strong approximants in each convex eventual
constraint set. This is the narrow Mazur step used for measure modulus. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma mem_closure_convex_of_weak_limit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : ℕ → E} {v : E} {S : Set E} (hS : Convex ℝ S)
    (hu : ∀ᶠ n in atTop, u n ∈ S)
    (hw : ∀ w : E, Tendsto (fun n => inner ℝ (u n) w) atTop (𝓝 (inner ℝ v w))) :
    v ∈ closure S := by
  by_contra hv
  obtain ⟨L,c,hL,hLv⟩ := geometric_hahn_banach_closed_point hS.closure isClosed_closure hv
  let w : E := (InnerProductSpace.toDual ℝ E).symm L
  have he (x : E) : inner ℝ x w = L x := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hl : Tendsto (fun n => L (u n)) atTop (𝓝 (L v)) := by
    simpa only [he] using hw w
  have hvle : L v ≤ c := le_of_tendsto hl (hu.mono (fun n hn => (hL _ (subset_closure hn)).le))
  exact (not_lt_of_ge hvle) hLv

lemma exists_strong_approximation_of_convex_eventual_constraints
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : ℕ → E} {v : E} (S : ℕ → Set E) (hS : ∀ n, Convex ℝ (S n))
    (hu : ∀ n, ∀ᶠ k in atTop, u k ∈ S n)
    (hw : ∀ w : E, Tendsto (fun n => inner ℝ (u n) w) atTop (𝓝 (inner ℝ v w))) :
    ∃ a : ℕ → E, (∀ n, a n ∈ S n) ∧ Tendsto a atTop (𝓝 v) := by
  have hex (n : ℕ) : ∃ x ∈ S n, dist x v < 1 / ((n : ℝ)+1) := by
    have hc := mem_closure_convex_of_weak_limit (hS n) (hu n) hw
    simpa only [dist_comm] using Metric.mem_closure_iff.mp hc
      (1 / ((n : ℝ)+1)) (by positivity)
  choose a ha hd using hex
  refine ⟨a,ha,?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun n => dist_nonneg) (fun n => (hd n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end CircleDomainRigidity

end

end OAI
