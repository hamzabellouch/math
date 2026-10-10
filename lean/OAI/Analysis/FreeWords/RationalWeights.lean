import Mathlib

namespace OAI

noncomputable section

namespace KKProjectionSupport

noncomputable section

theorem round_probability_weights {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i=1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : 0 < n) (k : ι → ℕ) (r : ℕ),
      (∑ i, k i)+r=n ∧ (∀ i, (k i:ℝ)/(n:ℝ) ≤ w i) ∧ (r:ℝ)/(n:ℝ) < ε := by
  classical
  obtain ⟨n,hn⟩ := exists_nat_gt (max (1:ℝ) ((Fintype.card ι : ℝ)/ε))
  have hn0 : 0 < n := by
    have : (0:ℝ) < n := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hn)
    exact_mod_cast this
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  let k : ι → ℕ := fun i => ⌊(n:ℝ)*w i⌋₊
  have hk (i : ι) : (k i : ℝ) ≤ (n:ℝ)*w i := Nat.floor_le (mul_nonneg hnr.le (hw i))
  have hkn : (∑ i, k i) ≤ n := by
    have hh := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hk i)
    rw [← Finset.mul_sum,h1,mul_one,← Nat.cast_sum] at hh
    exact_mod_cast hh
  let r := n-∑ i, k i
  refine ⟨n,hn0,k,r,Nat.add_sub_of_le hkn,?_,?_⟩
  · intro i
    exact (div_le_iff₀ hnr).mpr (by simpa only [mul_comm] using hk i)
  · have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) =>
      (Nat.lt_floor_add_one ((n:ℝ)*w i)).le)
    change (∑ i, (n:ℝ)*w i) ≤ ∑ i, ((k i:ℝ)+1) at hsum
    rw [← Finset.mul_sum,h1,mul_one,Finset.sum_add_distrib,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,mul_one,← Nat.cast_sum] at hsum
    have hr : (r:ℝ) ≤ (Fintype.card ι:ℝ) := by
      dsimp only [r]
      rw [Nat.cast_sub hkn]
      linarith
    have hcard : (Fintype.card ι:ℝ)/(n:ℝ) < ε := by
      apply (div_lt_iff₀ hnr).mpr
      have hn' := (le_max_right (1:ℝ) ((Fintype.card ι:ℝ)/ε)).trans_lt hn
      have hh := (div_lt_iff₀ hε).mp hn'
      nlinarith
    exact (div_le_div_of_nonneg_right hr hnr.le).trans_lt hcard

end

end KKProjectionSupport
end

end OAI
