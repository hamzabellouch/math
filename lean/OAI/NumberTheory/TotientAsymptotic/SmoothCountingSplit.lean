import OAI.NumberTheory.TotientAsymptotic.SmoothCofactorTail
import OAI.NumberTheory.TotientAsymptotic.MertensProduct

namespace OAI

/-! A finite counting version of the elementary smooth-number Rankin bound. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma card_le_endpoint_reciprocal (Q : Finset ℕ) (x : ℝ)
    (hQ : ∀ n ∈ Q,0 < n ∧ (n:ℝ) ≤ x) :
    (Q.card:ℝ) ≤ x*(∑ n ∈ Q,(n:ℝ)⁻¹) := by
  rw [Finset.mul_sum]
  calc
    (Q.card:ℝ) = ∑ _n ∈ Q,(1:ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (hQ n hn).1
      exact (one_le_div hn0).mpr (hQ n hn).2

lemma smooth_counting_split {K : ℕ} (hK : 2 ≤ K) (N : ℕ) (Z : ℝ)
    (Q : Finset ℕ) (hQ : ∀ n ∈ Q,0 < n ∧ n ≤ N ∧ largestPrimeFactor n ≤ K) :
    (Q.card:ℝ) ≤ Real.exp Z+
      N*Real.exp (-Z/(4*Real.log K))*(primeEulerProduct K)^4 := by
  classical
  let A : Finset ℕ := Q.filter (fun n : ℕ => (n:ℝ) ≤ Real.exp Z)
  let D : Finset ℕ := Q.filter (fun n : ℕ => ¬(n:ℝ) ≤ Real.exp Z)
  have hA : (A.card:ℝ) ≤ Real.exp Z := by
    have hs : A ⊆ Finset.Icc 1 ⌊Real.exp Z⌋₊ := by
      intro n hn
      obtain ⟨hn,hh⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_Icc.mpr ⟨(hQ n hn).1,Nat.le_floor hh⟩
    have hh : A.card ≤ ⌊Real.exp Z⌋₊ := by simpa using Finset.card_le_card hs
    exact (show (A.card:ℝ) ≤ (⌊Real.exp Z⌋₊:ℝ) by exact_mod_cast hh).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hD := card_le_endpoint_reciprocal D N (by
    intro n hn
    have hh := hQ n (Finset.mem_filter.mp hn).1
    exact ⟨hh.1,by exact_mod_cast hh.2.1⟩)
  have hrec : (∑ n ∈ D,(n:ℝ)⁻¹) ≤ ∑ n ∈ D,(n.totient:ℝ)⁻¹ := by
    apply Finset.sum_le_sum
    intro n hn
    have hn0 := (hQ n (Finset.mem_filter.mp hn).1).1
    apply (inv_le_inv₀ (by exact_mod_cast hn0)
      (by exact_mod_cast Nat.totient_pos.mpr hn0)).mpr
    exact_mod_cast Nat.totient_le n
  have htail := smooth_cofactor_rankin hK Z D (by
    intro n hn
    obtain ⟨hn,hh⟩ := Finset.mem_filter.mp hn
    have hz : Real.exp Z < (n:ℝ) := lt_of_not_ge hh
    exact ⟨(hQ n hn).1,(hQ n hn).2.2,(Real.lt_log_iff_exp_lt (by exact_mod_cast (hQ n hn).1)).mpr hz⟩)
  have hcard : (Q.card:ℝ) = (A.card:ℝ)+(D.card:ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s:=Q) (p:=fun n => (n:ℝ) ≤ Real.exp Z)).symm
  rw [hcard]
  have hh := mul_le_mul_of_nonneg_left (hrec.trans htail) (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  calc
    _ ≤ Real.exp Z+(N*(Real.exp (-Z/(4*Real.log K))*(primeEulerProduct K)^4)) :=
      add_le_add hA (hD.trans hh)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
