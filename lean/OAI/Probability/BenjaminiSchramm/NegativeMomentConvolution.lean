import OAI.Probability.BenjaminiSchramm.UpperMomentConvolution

namespace OAI

noncomputable section
open scoped BigOperators

namespace Percolation.BenjaminiSchramm

lemma normalized_negative_square_convolution_bound (S : ℕ → ℝ)
    (hS : ∀ n, 0 ≤ S n) (β K χ : ℝ) (hβ : 0 < β) (hχ : 0 ≤ χ)
    (hbound : ∀ n, S n ≤ χ) (hmul : ∀ n j, S (n+j) ≤ S n*S j)
    (hdecay : ∀ n : ℕ, S n ≤ K*Real.exp (-(3*β/4)*n)) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      Summable (fun j => (S (n+j))^2) ∧
      (∑' j : ℕ, (S (n+j))^2) ≤
        D*Real.exp (-β*n)*prefixMaximum (fun j => Real.exp (β*j)*S j) n := by
  have hgeom : Summable (fun j : ℕ => K^2*Real.exp (-(3*β/2)*j)) := by
    apply Summable.mul_left
    simpa only [mul_comm] using
      (Real.summable_exp_nat_mul_iff.mpr (by linarith : -(3*β/2) < 0))
  have hsqbound (j : ℕ) : (S j)^2 ≤ K^2*Real.exp (-(3*β/2)*j) := by
    calc
      _ ≤ (K*Real.exp (-(3*β/4)*j))^2 := pow_le_pow_left₀ (hS j) (hdecay j) 2
      _ = _ := by
        rw [mul_pow,pow_two (Real.exp _),←Real.exp_add]
        congr 2
        ring
  have hsq : Summable (fun j : ℕ => (S j)^2) :=
    hgeom.of_nonneg_of_le (fun j => sq_nonneg _) hsqbound
  let B : ℝ := ∑' j : ℕ, (S j)^2
  have hB : 0 ≤ B := tsum_nonneg fun _ => sq_nonneg _
  refine ⟨χ*B+1,by positivity,fun n => ?_⟩
  have hpoint (j : ℕ) : (S (n+j))^2 ≤ (S n)^2*(S j)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (hS (n+j)) (hmul n j) 2
  have hnsq : Summable (fun j : ℕ => (S (n+j))^2) :=
    (hsq.mul_left ((S n)^2)).of_nonneg_of_le (fun _ => sq_nonneg _) hpoint
  refine ⟨hnsq,?_⟩
  let H : ℕ → ℝ := fun j => Real.exp (β*j)*S j
  let M := prefixMaximum H n
  have hM : 0 ≤ M := (mul_nonneg (Real.exp_pos _).le (hS 0)).trans
    (le_prefixMaximum H (Nat.zero_le n))
  have he : S n=Real.exp (-β*n)*H n := by
    dsimp only [H]
    rw [←mul_assoc,←Real.exp_add,show -β*(n : ℝ)+β*n=0 by ring,Real.exp_zero,one_mul]
  have hSn : (S n)^2 ≤ χ*Real.exp (-β*n)*M := by
    calc
      _ = S n*(Real.exp (-β*n)*H n) := by rw [←he]; ring
      _ ≤ χ*(Real.exp (-β*n)*M) :=
        mul_le_mul (hbound n) (mul_le_mul_of_nonneg_left
          (le_prefixMaximum H le_rfl) (Real.exp_pos _).le)
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hS n))) hχ
      _ = _ := (mul_assoc _ _ _).symm
  calc
    _ ≤ ∑' j : ℕ, (S n)^2*(S j)^2 := hnsq.tsum_le_tsum hpoint (hsq.mul_left _)
    _ = (S n)^2*B := by rw [hsq.tsum_mul_left]
    _ ≤ (χ*Real.exp (-β*n)*M)*B := mul_le_mul_of_nonneg_right hSn hB
    _ = (χ*B)*Real.exp (-β*n)*M := by ring
    _ ≤ (χ*B+1)*Real.exp (-β*n)*M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end Percolation.BenjaminiSchramm

end

end OAI
