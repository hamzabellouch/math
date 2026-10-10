import OAI.Probability.BenjaminiSchramm.PrefixMaximumBootstrap
import OAI.Probability.BenjaminiSchramm.LayerMomentFekete

namespace OAI

noncomputable section
open scoped BigOperators

namespace Percolation.BenjaminiSchramm

lemma normalized_upper_convolution_bound (S : ℕ → ℝ) (hS : ∀ n, 0 ≤ S n)
    (β K : ℝ) (hβ : 0 < β)
    (hdecay : ∀ n : ℕ, S n ≤ K*Real.exp (-(3*β/4)*n)) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ,
      (∑ i ∈ Finset.range (n+1), S i*(S (n-i))^2) ≤
        A*Real.exp (-β*n)*prefixMaximum (fun j => Real.exp (β*j)*S j) n := by
  let H : ℕ → ℝ := fun j => Real.exp (β*j)*S j
  let g : ℕ → ℝ := fun j => Real.exp (-β/2*j)
  have hg : Summable g := by
    simpa only [g,mul_comm] using
      (Real.summable_exp_nat_mul_iff.mpr (by linarith : -β/2 < 0))
  have hg0 : ∀ j, 0 ≤ g j := fun _ => (Real.exp_pos _).le
  let B := K^2*∑' j, g j
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg K) (tsum_nonneg hg0)
  refine ⟨B+1,by linarith,fun n => ?_⟩
  let M := prefixMaximum H n
  have hM : 0 ≤ M := (mul_nonneg (Real.exp_pos _).le (hS 0)).trans
    (le_prefixMaximum H (Nat.zero_le n))
  have hs (i : ℕ) (hi : i ≤ n) : S i=Real.exp (-β*i)*H i := by
    dsimp only [H]
    rw [←mul_assoc,←Real.exp_add,show -β*(i : ℝ)+β*i=0 by ring,Real.exp_zero,one_mul]
  have hp (i : ℕ) (hi : i ≤ n) :
      S i*(S (n-i))^2 ≤ Real.exp (-β*n)*M*K^2*g (n-i) := by
    have hsum : (i : ℝ)+(n-i : ℕ)=n := by exact_mod_cast (Nat.add_sub_of_le hi)
    calc
      _ = (Real.exp (-β*i)*H i)*(S (n-i))^2 := by rw [hs i hi]
      _ ≤ (Real.exp (-β*i)*M)*(K*Real.exp (-(3*β/4)*(n-i : ℕ)))^2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (le_prefixMaximum H hi) (Real.exp_pos _).le)
          (pow_le_pow_left₀ (hS (n-i)) (hdecay (n-i)) 2) (sq_nonneg _)
          (mul_nonneg (Real.exp_pos _).le hM)
      _ = Real.exp (-β*n)*M*K^2*g (n-i) := by
        have he : Real.exp (-β*i)*(Real.exp (-(3*β/4)*(n-i : ℕ)))^2 =
            Real.exp (-β*n)*g (n-i) := by
          rw [pow_two,←Real.exp_add,←Real.exp_add]
          dsimp only [g]
          rw [←Real.exp_add]
          congr 1
          nlinarith [hsum]
        calc
          _ = M*K^2*(Real.exp (-β*i)*(Real.exp (-(3*β/4)*(n-i : ℕ)))^2) := by ring
          _ = _ := by rw [he]; ring
  have hsumg : (∑ i ∈ Finset.range (n+1), g (n-i)) ≤ ∑' j, g j := by
    have he := Finset.sum_range_reflect g (n+1)
    simp only [Nat.add_sub_cancel] at he
    rw [he]
    exact hg.sum_le_tsum _ (fun j _ => hg0 j)
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), Real.exp (-β*n)*M*K^2*g (n-i) :=
      Finset.sum_le_sum fun i hi => hp i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _ = Real.exp (-β*n)*M*K^2*(∑ i ∈ Finset.range (n+1), g (n-i)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-β*n)*M*K^2*(∑' j, g j) :=
      mul_le_mul_of_nonneg_left hsumg (by positivity)
    _ = B*Real.exp (-β*n)*M := by dsimp only [B]; ring
    _ ≤ (B+1)*Real.exp (-β*n)*M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end Percolation.BenjaminiSchramm

end

end OAI
