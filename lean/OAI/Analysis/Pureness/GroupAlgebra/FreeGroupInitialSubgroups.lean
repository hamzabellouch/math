import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter

def initialFreeSubgroup (n : ℕ) : Subgroup (FreeGroup ℕ) :=
  Subgroup.closure (FreeGroup.of '' {k : ℕ | k < n})

lemma initialFreeSubgroup_mono : Monotone initialFreeSubgroup := by
  intro m n hmn
  apply Subgroup.closure_mono
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hmn, rfl⟩

lemma eventually_mem_initialFreeSubgroup (g : FreeGroup ℕ) :
    ∀ᶠ n in atTop, g ∈ initialFreeSubgroup n := by
  induction g using FreeGroup.induction_on with
  | one => exact Eventually.of_forall fun n => (initialFreeSubgroup n).one_mem
  | of k =>
    filter_upwards [eventually_gt_atTop k] with n hn
    exact Subgroup.subset_closure ⟨k, hn, rfl⟩
  | inv_of g hg =>
    filter_upwards [hg] with n hn
    exact (initialFreeSubgroup n).inv_mem hn
  | mul g h hg hh =>
    filter_upwards [hg, hh] with n hgn hhn
    exact (initialFreeSubgroup n).mul_mem hgn hhn
end CuntzPureness

end

end OAI
