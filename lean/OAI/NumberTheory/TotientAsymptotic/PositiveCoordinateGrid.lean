import OAI.NumberTheory.TotientAsymptotic.CappedLoglogGrid
import OAI.NumberTheory.TotientAsymptotic.ThirdPrimeSize

namespace OAI

/-! Simultaneous finite-grid rounding of all positive ordered coordinates. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def coordinateGridIndex (K n k : ℕ) (j : Fin k) : ℕ :=
  cappedLoglogIndex K (B (fordPrime n (j.val+1)))

def coordinateGridCutoff (L k : ℕ) (g : Fin k → ℕ) (j : ℕ) : ℕ :=
  if hj : j < k then loglogCutoff (g ⟨j,hj⟩) else loglogCutoff L

lemma positive_coordinate_grid {x : ℝ} {n k K L : ℕ}
    (hx : 4 ≤ x) (hn : 0 < n) (hφ : (n.totient:ℝ) ≤ x)
    (hL : 3 ≤ L) (hLK : L ≤ K) (hK : (K:ℝ) ≤ B x+2)
    (hpositive : ∀ j : Fin k,(L:ℝ)+1 ≤ B (fordPrime n (j.val+1))) :
    let g := coordinateGridIndex K n k
    (∀ j : Fin k,L ≤ g j ∧ g j ≤ K ∧
      loglogCutoff (g j) < fordPrime n (j.val+1) ∧
      B (loglogCutoff (g j)) ≤ K ∧
      Real.log (loglogCutoff (g j)) ≤ Real.exp K ∧
      j.val+2 ≤ n.primeFactorsList.length) ∧
    (∀ i j : Fin k,i ≤ j → g j ≤ g i) ∧
    (∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1))-
      (B x+5-K)*(∑ j : Fin k,a (j.val+1)) ≤
      ∑ j : Fin k,a (j.val+1)*B (loglogCutoff (g j)) := by
  let g := coordinateGridIndex K n k
  have hraw (j : Fin k) : 4 ≤ B (fordPrime n (j.val+1)) := by
    have hh : (3:ℝ) ≤ L := by exact_mod_cast hL
    linarith [hpositive j]
  have hidx (j : Fin k) : j.val+1 < n.primeFactorsList.length :=
    fordPrime_index_of_doubleLog_pos (lt_of_lt_of_le (by norm_num) (hraw j))
  have hc (j : Fin k) : fordPrimeCoordinate n (j.val+1)=B (fordPrime n (j.val+1)) :=
    max_eq_right (by change 0 ≤ B (fordPrime n (j.val+1)); linarith [hraw j])
  have hb (j : Fin k) : B (fordPrime n (j.val+1)) ≤ B x+2 := by
    rw [← hc j]
    exact ford_coordinate_upper hx hn hφ _
  have hg (j : Fin k) := capped_loglog_prime (show 2 ≤ K by omega) hK
    (fordPrime_prime (hidx j)).one_lt (hraw j) (hb j)
  refine ⟨?_,?_,?_⟩
  · intro j
    exact ⟨cappedLoglogIndex_lower hLK (hpositive j),(hg j).2.1,(hg j).2.2.1,
      (hg j).2.2.2.2.1,(hg j).2.2.2.2.2,by have := hidx j; omega⟩
  · intro i j hij
    apply cappedLoglogIndex_mono K
    have hh := ford_coordinate_antitone n (show i.val+1 ≤ j.val+1 by exact Nat.add_le_add_right hij 1)
    rwa [hc i,hc j] at hh
  · have hterm (j : Fin k) :
        a (j.val+1)*fordPrimeCoordinate n (j.val+1)-(B x+5-K)*a (j.val+1) ≤
        a (j.val+1)*B (loglogCutoff (g j)) := by
      have hh := mul_le_mul_of_nonneg_left (hg j).2.2.2.1 (a_pos (show 0 < j.val+1 by omega)).le
      rw [hc j]
      dsimp [g,coordinateGridIndex]
      nlinarith only [hh]
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun (j : Fin k) _ => hterm j)
    simpa only [Finset.sum_sub_distrib,← Finset.mul_sum] using hs

lemma coordinate_grid_cutoff_terminal (L k : ℕ) (g : Fin k → ℕ) :
    coordinateGridCutoff L k g k=loglogCutoff L := by simp [coordinateGridCutoff]

lemma coordinate_grid_cutoff_descending {L k : ℕ} {g : Fin k → ℕ}
    (hL : ∀ j,L ≤ g j) (hmono : ∀ i j : Fin k,i ≤ j → g j ≤ g i) :
    ∀ j < k,coordinateGridCutoff L k g (j+1) ≤ coordinateGridCutoff L k g j := by
  intro j hj
  by_cases hj1 : j+1 < k
  · simp only [coordinateGridCutoff,hj,hj1,dite_eq_left]
    exact loglogCutoff_mono (by exact_mod_cast hmono ⟨j,hj⟩ ⟨j+1,hj1⟩ (by simp))
  · simp only [coordinateGridCutoff,hj,hj1,dite_eq_left]
    exact loglogCutoff_mono (by exact_mod_cast hL ⟨j,hj⟩)

end TotientAsymptotic

end

end OAI
