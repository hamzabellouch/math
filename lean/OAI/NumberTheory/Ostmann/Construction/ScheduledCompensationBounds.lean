import OAI.NumberTheory.Ostmann.Construction.ScheduledIntegerRigidity
import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedCompensationPrior

namespace OAI

/-! # The integer pivot cap bounds the actual selected compensation product -/
namespace Ostmann
open scoped Classical BigOperators

theorem selected_scheduled_pivot_bound
    {A B : Set ℕ} {N hi top : ℕ} {a C L X G : ℝ} {D P : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (hcs : List.Forall₂ (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j)
      cs targets) (n : ℕ) (hn : n < cs.length)
    (u : TreeLeafIndex n × Fin 4 → P)
    (hu : (∏ i, completedCompensationPrior A B N X hi D P top cs n (u i)) ≠ 0)
    (p : ℕ) (hp : p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊) :
    p * (∏ i, (u i : ℕ)) ≤ scheduledPivotBound G cs n := by
  have hc := forall₂_headD_drop hcs n hn
  have hprime (i : TreeLeafIndex n × Fin 4) :
      (u i : ℝ) ≤ Real.exp (((cs.drop n).headD 0 : ℝ) + 1) := by
    have hnz := Finset.prod_ne_zero_iff.mp hu i (Finset.mem_univ i)
    rw [completedCompensationPrior_used A B N X hi D P top cs n hn] at hnz
    have hmem := primeSubsetPrior_support P _ (u i) hnz
    exact (hc.2.2.2.2.2.2 _ hmem).2.2.1
  have hprod := Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) => by positivity :
      ∀ i ∈ Finset.univ, 0 ≤ (u i : ℝ)) (fun i _ => hprime i)
  have hprod' : ((∏ i, (u i : ℕ) : ℕ) : ℝ) ≤
      Real.exp ((2 : ℝ) ^ n * 4 * (((cs.drop n).headD 0 : ℝ) + 1)) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, card_treeLeafIndex,
      Fintype.card_fin, ← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_prod] using hprod
  have hpFloor : (p : ℝ) ≤ (⌊Real.exp (G + 1)⌋₊ : ℝ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hp).2
  have hp' : (p : ℝ) ≤ Real.exp (G + 1) :=
    hpFloor.trans (Nat.floor_le (Real.exp_nonneg _))
  have htotal := mul_le_mul hp' hprod' (by positivity) (Real.exp_nonneg _)
  rw [← Real.exp_add, ← Nat.cast_mul] at htotal
  have hfinal : ((p * ∏ i, (u i : ℕ) : ℕ) : ℝ) ≤
      (scheduledPivotBound G cs n : ℝ) := htotal.trans (Nat.le_ceil _)
  exact_mod_cast hfinal

end Ostmann

end OAI
