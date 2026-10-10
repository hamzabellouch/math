import OAI.Combinatorics.ContingencyTables.Transport.TranslatedCompletionAcceptance
import OAI.Combinatorics.ContingencyTables.Sampling.SmallChainBudget

namespace OAI

/-! # Half acceptance at the paper's actual padding scale -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
lemma padding_ge_twenty_dimension (d : ℕ) (hd : 14 ≤ d) : 20*d ≤ d^12 := by
  have hp : 20 ≤ d^11 :=
    (by norm_num : 20 ≤ 14^11).trans (Nat.pow_le_pow_left hd 11)
  calc
    _ ≤ d^11*d := Nat.mul_le_mul_right d hp
    _ = _ := by ring

/-- Only the literal reference row and column are union bounded. -/
theorem reference_acceptance_half
    (R : Option I → ℕ) (P : Option J → ℕ) (D : Option I → Option J → ℤ)
    (htotal : (∑ i,R i)=∑ j,P j)
    (hzero : ∀ i j,D (some i) (some j)=0)
    (d : ℕ) (hd : 14 ≤ d)
    (hrows : Fintype.card (Option I) ≤ d) (hcols : Fintype.card (Option J) ≤ d)
    (hcross : Fintype.card I+Fintype.card J+1 ≤ d)
    (hrow : ∀ i,d^12 ≤ R i) (hcol : ∀ j,d^12 ≤ P j)
    (hbound : ∀ i j,|D i j| ≤ (10*d:ℕ)) :
    (Fintype.card (Table R P):ℝ)/2 ≤ Fintype.card (Accepted R P D) := by
  have hpad := padding_ge_twenty_dimension d hd
  have ht : 2*(10*d) ≤ d^12 := by omega
  have hfour : 4*d ≤ d^12 := by omega
  have hfrac := reference_acceptance R P D htotal hzero (d^12) d (10*d)
    (by omega) hrows hcols hrow hcol hfour ht hbound
  have hcrossR : (Fintype.card I+Fintype.card J+1:ℕ) ≤ (d:ℝ) := by exact_mod_cast hcross
  have hu : ((Fintype.card I+Fintype.card J+1:ℕ):ℝ)*
      (4*(10*d:ℕ)*(d:ℝ)^3/(d^12:ℕ)) ≤ 40*(d:ℝ)^5/(d^12:ℕ) := by
    calc
      _ ≤ (d:ℝ)*(4*(10*d:ℕ)*(d:ℝ)^3/(d^12:ℕ)) :=
        mul_le_mul_of_nonneg_right hcrossR (by positivity)
      _ = _ := by push_cast; ring
  have he := completion_rejection_lt_half d hd
  have hc : (0:ℝ) < Fintype.card (Table R P) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (table_nonempty R P htotal)
  have hh : (1/2:ℝ) ≤ (Fintype.card (Accepted R P D):ℝ)/Fintype.card (Table R P) := by linarith
  have hm := (le_div_iff₀ hc).mp hh
  linarith

end ContingencyTables.CompletionTranslation

end OAI
