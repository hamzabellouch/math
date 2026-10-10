import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepeatedRenamingBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicScope

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryRepeatedRenaming
open Characters.RationalHistory HistorySymbolicScope
variable {ι κ : Type*}

theorem above_rename (e : Expr ι) (f : ι → κ)
    (sourceLevel : ι → ℕ) (targetLevel : κ → ℕ)
    (hlevel : ∀ i, targetLevel (f i) = sourceLevel i) (t : ℕ) :
    Above targetLevel t (e.rename f) ↔ Above sourceLevel t e := by
  induction e <;> simp_all [Expr.rename, Above]

theorem fraction_vars_above [DecidableEq κ] (e : Expr ι) (f : ι → κ)
    (sourceLevel : ι → ℕ) (targetLevel : κ → ℕ)
    (hlevel : ∀ i, targetLevel (f i) = sourceLevel i) (t : ℕ)
    (he : Above sourceLevel t e) :
    (∀ j ∈ (e.rename f).numerator.vars, t < targetLevel j) ∧
    (∀ j ∈ (e.rename f).denominator.vars, t < targetLevel j) := by
  have ha := above_atoms (e.rename f)
    ((above_rename e f sourceLevel targetLevel hlevel t).mpr he)
  exact ⟨fun j hj => ha j ((e.rename f).fraction_vars_subset.1 hj),
    fun j hj => ha j ((e.rename f).fraction_vars_subset.2 hj)⟩

theorem type_excluded [DecidableEq κ] (e : Expr ι) (f : ι → κ)
    (sourceLevel : ι → ℕ) (targetLevel : κ → ℕ)
    (hlevel : ∀ i, targetLevel (f i) = sourceLevel i) (t : ℕ)
    (he : Above sourceLevel t e) (j : κ) (hj : targetLevel j ≤ t) :
    j ∉ (e.rename f).atoms ∧
    j ∉ (e.rename f).numerator.vars ∧ j ∉ (e.rename f).denominator.vars := by
  have ha : j ∉ (e.rename f).atoms := by
    intro hm
    exact (not_lt_of_ge hj) (above_atoms (e.rename f)
      ((above_rename e f sourceLevel targetLevel hlevel t).mpr he) j hm)
  exact ⟨ha, fun hm => ha ((e.rename f).fraction_vars_subset.1 hm),
    fun hm => ha ((e.rename f).fraction_vars_subset.2 hm)⟩

theorem setZero_type_excluded [DecidableEq κ] (e : Expr ι) (f : ι → κ)
    (sourceLevel : ι → ℕ) (targetLevel : κ → ℕ)
    (hlevel : ∀ i, targetLevel (f i) = sourceLevel i) (t : ℕ)
    (he : Above sourceLevel t e) (j : κ) (hj : targetLevel j ≤ t) :
    Characters.ZeroVariable.setZero j (e.rename f).numerator = (e.rename f).numerator ∧
    Characters.ZeroVariable.setZero j (e.rename f).denominator = (e.rename f).denominator := by
  have ha := (type_excluded e f sourceLevel targetLevel hlevel t he j hj).1
  exact ⟨(e.rename f).setZero_numerator_of_not_mem j ha,
    (e.rename f).setZero_denominator_of_not_mem j ha⟩

end Ostmann.Arithmetic.HistoryRepeatedRenaming
end

end OAI
