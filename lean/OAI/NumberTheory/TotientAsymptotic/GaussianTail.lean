import OAI.NumberTheory.TotientAsymptotic.ProjectedGaussian

namespace OAI

/-! Finite Gaussian tails with the same exponent at the first index. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_gaussian_tail (Q : Finset ℕ) (Ψ : ℕ) (hQ : ∀ k ∈ Q, Ψ ≤ k) :
    (∑ k ∈ Q,Real.exp (-(k:ℝ)^2/4)) ≤
      Real.exp (-(Ψ:ℝ)^2/4)/(1-Real.exp (-1/4:ℝ)) := by
  classical
  let q : ℝ := Real.exp (-1/4:ℝ)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hterm (k : ℕ) (hk : k ∈ Q) :
      Real.exp (-(k:ℝ)^2/4) ≤ Real.exp (-(Ψ:ℝ)^2/4)*q^(k-Ψ) := by
    have hsub : (k:ℝ)=(Ψ:ℝ)+(k-Ψ:ℕ) := by
      exact_mod_cast (Nat.add_sub_of_le (hQ k hk)).symm
    have hd : (k-Ψ:ℕ) ≤ ((k-Ψ:ℕ):ℝ)^2 := by
      by_cases hz : k-Ψ=0
      · simp [hz]
      · have hh : (1:ℝ) ≤ (k-Ψ:ℕ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
        nlinarith
    have hΨ : (0:ℝ) ≤ Ψ := Nat.cast_nonneg Ψ
    have hd0 : (0:ℝ) ≤ (k-Ψ:ℕ) := Nat.cast_nonneg _
    have hex : q^(k-Ψ)=Real.exp (-((k-Ψ:ℕ):ℝ)/4) := by
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hex,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hsub,hd,hΨ,hd0]
  have hinj : Set.InjOn (fun k : ℕ => k-Ψ) ↑Q := by
    intro k hk l hl he
    have hkΨ := hQ k hk
    have hlΨ := hQ l hl
    change k-Ψ=l-Ψ at he
    omega
  have hsum : (∑ k ∈ Q,q^(k-Ψ)) ≤ 1/(1-q) := by
    rw [← Finset.sum_image hinj]
    have hs := hasSum_geometric_of_lt_one hq hq1
    simpa only [one_div] using
      (hs.summable.sum_le_tsum _ (fun i _ => pow_nonneg hq i)).trans_eq hs.tsum_eq
  calc
    _ ≤ ∑ k ∈ Q,Real.exp (-(Ψ:ℝ)^2/4)*q^(k-Ψ) := Finset.sum_le_sum hterm
    _ = Real.exp (-(Ψ:ℝ)^2/4)*(∑ k ∈ Q,q^(k-Ψ)) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(Ψ:ℝ)^2/4)*(1/(1-q)) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = _ := by dsimp [q]; ring

end TotientAsymptotic

end

end OAI
