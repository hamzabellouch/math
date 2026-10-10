import OAI.Analysis.CircleDomains.Selection.PositiveJumpCount
import Mathlib.Data.Finset.Lattice.Fold

namespace OAI

/-! Finitely many positive old tolls and the positive new-jump floor have
one common positive real lower bound. -/

open scoped ENNReal

namespace CircleDomainRigidity

theorem exists_common_positive_jump_floor {I : Type*} [Fintype I]
    (r : ℝ≥0∞) (hr : 0 < r) (T : I → ℝ≥0∞) (hT : ∀i, 0 < T i) :
    ∃δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r ∧ ∀i, ENNReal.ofReal δ ≤ T i := by
  classical
  let c : Option I → ℝ≥0∞ := fun i => i.elim r T
  have hne : (Finset.univ : Finset (Option I)).Nonempty := ⟨none, Finset.mem_univ _⟩
  have hc : 0 < Finset.univ.inf' hne c := by
    apply (Finset.lt_inf'_iff hne).mpr
    intro i _
    cases i with
    | none => exact hr
    | some i => exact hT i
  obtain ⟨δ, hδ, hd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hc
  have hle (i : Option I) : ENNReal.ofReal (δ : ℝ) ≤ c i := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hd.le.trans (Finset.inf'_le c (Finset.mem_univ i))
  refine ⟨δ, ?_, hle none, fun i => hle (some i)⟩
  exact_mod_cast (ENNReal.coe_pos.mp hδ)

end CircleDomainRigidity

end OAI
