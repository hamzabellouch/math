import Mathlib
import OAI.Combinatorics.UniformKServer.PrefixMovement

namespace OAI

                                        
section

/-! Key-count L1 drift from the coupled literal member keys. -/
noncomputable section
namespace UniformKServer.KeyCountVariation
open Finset
open scoped Classical
variable {L : Type*} [Fintype L] {k : ℕ}

def indicator (p l : L) : ℝ := if p=l then 1 else 0

def count (p : Fin k→L) (l : L) : ℝ := ∑ a,indicator (p a) l

theorem single (p q : L) : (∑ l,|indicator p l-indicator q l|)≤2*PrefixMovement.diff p q := by
  by_cases he : p=q
  · subst q
    simp [PrefixMovement.diff]
  · have h (l : L) : |indicator p l-indicator q l|≤ indicator p l+indicator q l := by
      unfold indicator
      split_ifs <;> norm_num
    have hs := sum_le_sum (fun l (_ : l∈univ)=>h l)
    norm_num [indicator,PrefixMovement.diff,he,sum_add_distrib] at hs ⊢
    exact hs

theorem total (p q : Fin k→L) : (∑ l,|count p l-count q l|)≤2*∑ a,PrefixMovement.diff (p a) (q a) := by
  calc
    _≤∑ l,∑ a,|indicator (p a) l-indicator (q a) l| := by
      apply sum_le_sum
      intro l _
      unfold count
      rw [←sum_sub_distrib]
      exact abs_sum_le_sum_abs _ _
    _=∑ a,∑ l,|indicator (p a) l-indicator (q a) l| := sum_comm
    _≤∑ a,2*PrefixMovement.diff (p a) (q a) := sum_le_sum (fun a _=>single (p a) (q a))
    _=_ := (mul_sum ..).symm

end UniformKServer.KeyCountVariation

end


end

end OAI
