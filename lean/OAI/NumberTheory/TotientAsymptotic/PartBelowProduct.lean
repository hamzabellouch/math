import OAI.NumberTheory.TotientAsymptotic.PrimeFactorBands

namespace OAI

/-! The small-prime part commutes with a finite product of nonzero integers. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBelow_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s,f i ≠ 0) (V : ℝ) :
    partBelow (∏ i ∈ s,f i) V=∏ i ∈ s,partBelow (f i) V := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [partBelow]
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hfs : ∀ j ∈ s,f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,partBelow_mul hfi (Finset.prod_ne_zero_iff.mpr hfs),
      Finset.prod_insert hi,ih hfs]

end TotientAsymptotic

end

end OAI
