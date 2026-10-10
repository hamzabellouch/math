import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

namespace OAI

/-! # A short inward segment for finitely many facet inequalities -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W I : Type*} [AddCommGroup W] [Module ℝ W] [Fintype I]

/-- A direction pointing inward at every active constraint stays in the
polyhedron for one common positive interval. -/
theorem exists_inward_facet_interval
    (α : I → W →ₗ[ℝ] ℝ) (c : I → ℝ) (p v : W)
    (hp : ∀ i, α i p ≤ c i)
    (hv : ∀ i, α i p = c i → 0 ≤ α i v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Icc (0 : ℝ) ε, ∀ i, α i (p - t • v) ≤ c i := by
  classical
  let bound : Option I → ℝ := fun o => o.elim 1 fun i =>
    if α i v < 0 then (c i - α i p) / (1 - α i v) else 1
  have hb : ∀ o, 0 < bound o := by
    intro o
    cases o with
    | none => exact zero_lt_one
    | some i =>
      dsimp only [bound, Option.elim_some]
      split_ifs with h
      · have hlt : α i p < c i := lt_of_le_of_ne (hp i) (by
          intro he
          exact (not_le_of_gt h) (hv i he))
        exact div_pos (sub_pos.mpr hlt) (by linarith)
      · exact zero_lt_one
  let ε := Finset.univ.inf' Finset.univ_nonempty bound
  have hε : 0 < ε := (Finset.lt_inf'_iff _).mpr (fun o _ => hb o)
  refine ⟨ε, hε, ?_⟩
  intro t ht i
  simp only [map_sub, map_smul, smul_eq_mul]
  by_cases hn : α i v < 0
  · have hbound : ε ≤ (c i - α i p) / (1 - α i v) := by
      have hh := Finset.inf'_le (f := bound) (Finset.mem_univ (some i))
      simpa only [bound, Option.elim_some, ite_eq_left hn] using hh
    have hh := (le_div_iff₀ (by linarith : 0 < 1 - α i v)).mp
      (ht.2.trans hbound)
    nlinarith [ht.1]
  · have := hp i
    nlinarith [mul_nonneg ht.1 (le_of_not_gt hn)]

end PolycyclicRecognition

end

end OAI
