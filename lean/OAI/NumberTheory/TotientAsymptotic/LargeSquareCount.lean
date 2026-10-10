import OAI.NumberTheory.TotientAsymptotic.PreimageLoglogBound
import Mathlib.Analysis.PSeries

namespace OAI

/-! Counts for repeated large prime factors in values and their preimages. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma large_square_count (N K : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q,0 < n ∧ n ≤ N ∧ ∃ d : ℕ,K < d ∧ d^2 ∣ n) :
    (Q.card:ℝ) ≤ 2*N/(K+1:ℕ) := by
  classical
  let P := Finset.Ioo K (N+1)
  let M := fun d : ℕ => (Finset.range (N+1)).filter (fun n => n ≠ 0 ∧ d^2 ∣ n)
  have hsub : Q ⊆ P.biUnion M := by
    intro n hn
    obtain ⟨hn0,hnN,d,hKd,hd⟩ := hQ n hn
    have hd1 : 1 ≤ d := by omega
    have hdn : d ≤ n := (by nlinarith : d ≤ d^2).trans (Nat.le_of_dvd hn0 hd)
    exact Finset.mem_biUnion.mpr ⟨d,Finset.mem_Ioo.mpr ⟨hKd,by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hn0.ne',hd⟩⟩
  have hterm (d : ℕ) (hd : d ∈ P) : ((M d).card:ℝ) ≤ N/(d:ℝ)^2 := by
    have hd0 : 0 < d := by have := (Finset.mem_Ioo.mp hd).1; omega
    have hh : (M d).card=N/d^2 := Nat.card_multiples' N (d^2)
    rw [hh]
    have hle : (N/d^2)*d^2 ≤ N := Nat.div_mul_le_self N (d^2)
    apply (le_div_iff₀ (sq_pos_of_pos (show (0:ℝ)<d by exact_mod_cast hd0))).mpr
    exact_mod_cast hle
  calc
    _ ≤ ((P.biUnion M).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ d ∈ P,((M d).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (P.biUnion M).card ≤ ∑ d ∈ P,(M d).card)
    _ ≤ ∑ d ∈ P,N/(d:ℝ)^2 := Finset.sum_le_sum hterm
    _ = N*(∑ d ∈ P,((d:ℝ)^2)⁻¹) := by rw [Finset.mul_sum]; simp only [div_eq_mul_inv]
    _ ≤ N*(2/(K+1:ℕ)) := mul_le_mul_of_nonneg_left
      (by simpa [P,Nat.cast_add,Nat.cast_one] using (sum_Ioo_inv_sq_le (α:=ℝ) K (N+1))) (Nat.cast_nonneg N)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
