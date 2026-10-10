import OAI.Combinatorics.ContingencyTables.Transport.BalancedCellFibres

namespace OAI

/-! # Partitioning actual balanced profiles into small and large cells -/

namespace ContingencyTables.BalancedCellFibres

open scoped BigOperators Classical
open PhysicalLargeProfiles LargePairEnumeration

variable {C : Type*}

abbrev SmallProfiles (small : C → Bool) (M : C → ℕ) :=
  (s : {c : C // small c=true}) → Fin (M s.val+1)

noncomputable def partition (small : C → Bool) (M : C → ℕ) :
    Profiles M ≃ SmallProfiles small M×PhysicalAssignments small M where
  toFun a := (fun s => a s.val,fun l => a l.val)
  invFun a c := if hs : small c=true then a.1 ⟨c,hs⟩
    else a.2 ⟨c,Bool.eq_false_iff.mpr hs⟩
  left_inv a := by funext c; dsimp only; split_ifs <;> rfl
  right_inv a := by
    apply Prod.ext
    · funext s
      simp only [s.property,dite_eq_left]
    · funext l
      simp only [l.property,Bool.false_eq_true,dite_false]

def smallDisplay (small : C → Bool) (M : C → ℕ) (a : SmallProfiles small M) : SmallView small → ℕ :=
  fun p => if p.2 then M p.1.val-(a p.1).val else (a p.1).val

lemma partition_profile (small : C → Bool) (M : C → ℕ)
    (a : SmallProfiles small M×PhysicalAssignments small M) :
    profile M ((partition small M).symm a)=
      physicalProfile small M (smallDisplay small M a.1) a.2 := by
  funext p
  rcases p with ⟨c,b⟩
  by_cases hs : small c=true
  · simp only [profile,partition,Equiv.coe_fn_symm_mk,physicalProfile,hs,dite_eq_left,smallDisplay]
  · simp only [profile,partition,Equiv.coe_fn_symm_mk,physicalProfile,hs,Bool.false_eq_true,dite_false]

variable [Fintype C]

/-- This exact finite product split removes all artificial labels and
enumerations from the companion's terminal normalizer. -/
theorem sum_eq_small_large (small : C → Bool) (M : C → ℕ)
    (F : (C×Bool → ℕ) → ℝ) :
    (∑ a : Profiles M,F (profile M a))=
      ∑ s : SmallProfiles small M,∑ a : PhysicalAssignments small M,
        F (physicalProfile small M (smallDisplay small M s) a) := by
  have he := Fintype.sum_equiv (partition small M)
    (fun a => F (profile M a))
    (fun a => F (physicalProfile small M (smallDisplay small M a.1) a.2))
    (by
      intro a
      have h := partition_profile small M ((partition small M) a)
      simpa only [Equiv.symm_apply_apply] using congrArg F h)
  rw [he,Fintype.sum_prod_type]

end ContingencyTables.BalancedCellFibres

end OAI
