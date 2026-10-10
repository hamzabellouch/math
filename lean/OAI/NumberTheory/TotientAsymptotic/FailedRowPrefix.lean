import OAI.NumberTheory.TotientAsymptotic.FirstFailedRow
import OAI.NumberTheory.TotientAsymptotic.RemainderSplit

namespace OAI

/-! The actual prime prefix before a first failed row belongs to the unbanded simplex. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma fordRowSum_truncate {K L j : ℕ} (hKL : K ≤ L) (u : ℕ → ℝ)
    (hu : ∀ r, 0 ≤ u r) : fordRowSum K u j ≤ fordRowSum L u j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    have hr := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.trans hKL⟩
  · intro r hr _
    have hr := Finset.mem_Icc.mp hr
    exact mul_nonneg (a_pos (by omega)).le (hu r)

lemma rows_give_enlarged_prefix {K L : ℕ} {x : ℝ} (hKL : K ≤ L)
    (u : ℕ → ℝ) (hu : ∀ r, 0 ≤ u r)
    (hrows : ∀ i ≤ K, fordRowSum L u i ≤ xi x i*(if i=0 then B x else u i)) :
    (fun i : Fin K => u (i.val+1)) ∈
      enlargedSimplex K (B x) (xi x 0) (fun i => xi x (i.val+1)) := by
  refine ⟨fun i => hu _,?_,?_⟩
  · intro i
    have hh := (fordRowSum_truncate (j:=i.val+1) hKL u hu).trans
      (hrows (i.val+1) (by have := i.isLt; omega))
    unfold fordRowSum at hh
    rw [prefix_sum_fin] at hh
    simpa only [Fin.lt_def,Nat.add_lt_add_iff_right,Nat.add_sub_add_right,Nat.add_eq_zero_iff,
      Nat.one_ne_zero,and_false,ite_false] using hh
  · have hh := (fordRowSum_truncate (j:=0) hKL u hu).trans (hrows 0 (Nat.zero_le _))
    unfold fordRowSum at hh
    rw [prefix_sum_fin] at hh
    simpa only [Nat.zero_lt_succ,ite_true,Nat.sub_zero] using hh

def fordPrefixPrimes (n K : ℕ) : Fin K → ℕ := fun i => fordPrime n (i.val+1)

theorem failed_row_prefix_conditions {x : ℝ} {n L j : ℕ}
    (hj : 2 ≤ j) (hjL : j ≤ L)
    (hrows : ∀ i < j, fordRowSum L (fordPrimeCoordinate n) i ≤
      xi x i*(if i=0 then B x else fordPrimeCoordinate n i))
    (hfail : xi x j*fordPrimeCoordinate n j < fordRowSum L (fordPrimeCoordinate n) j) :
    (∀ i, (fordPrefixPrimes n (j-1) i).Prime) ∧
    primePrefixCoord (fordPrefixPrimes n (j-1)) ∈
      enlargedSimplex (j-1) (B x) (xi x 0) (fun i => xi x (i.val+1)) ∧
    (∀ i, i.val+1=j-1 → (1/100:ℝ) ≤ primePrefixCoord (fordPrefixPrimes n (j-1)) i) := by
  have hp (i : Fin (j-1)) : 0 < fordPrimeCoordinate n (i.val+1) :=
    (failed_row_coordinate_pos hfail).trans_le (ford_coordinate_antitone n (by omega))
  have he : primePrefixCoord (fordPrefixPrimes n (j-1)) =
      fun i : Fin (j-1) => fordPrimeCoordinate n (i.val+1) := by
    funext i
    exact (fordPrimeCoordinate_eq_raw_of_pos (hp i)).symm
  refine ⟨fun i => fordPrime_prime (fordPrime_index_of_doubleLog_pos
    (by rw [← fordPrimeCoordinate_eq_raw_of_pos (hp i)]; exact hp i)),?_,?_⟩
  · rw [he]
    exact rows_give_enlarged_prefix (by omega) _ (fun _ => le_max_left _ _)
      (fun i hi => hrows i (by omega))
  · intro i _
    rw [he]
    exact positive_ford_coordinate_lower (hp i)

end TotientAsymptotic

end

end OAI
