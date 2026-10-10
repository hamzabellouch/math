import Mathlib.Data.Nat.Choose.Sum
import OAI.Geometry.NodalSets.Elliptic.ReciprocalDerivativeBound

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma frequency_product_derivative (f g : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x : E) (r a b : ℕ) {N A B H K : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(i+a)*H)
    (hgb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i g x‖ ≤ B*N^(i+b)*K) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*g y) x‖ ≤
      (2:ℝ)^r*A*B*N^(r+a+b)*(H*K) := by
  refine (norm_iteratedFDeriv_mul_le hf hg x
    (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (r+1), (r.choose i:ℝ)*(A*N^(i+a)*H)*
        (B*N^(r-i+b)*K) := by
      apply Finset.sum_le_sum
      intro i hi
      have hir : i ≤ r := by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfb i hir) (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg hA (pow_nonneg hN _)) hH))
        (hgb (r-i) (by omega))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg (mul_nonneg hB (pow_nonneg hN _)) hK)
    _ = (∑ i ∈ Finset.range (r+1), (r.choose i:ℝ))*(A*B*N^(r+a+b)*(H*K)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≤ r := by have := Finset.mem_range.mp hi; omega
      have hp : N^(i+a)*N^(r-i+b) = N^(r+a+b) := by rw [← pow_add]; congr 1; omega
      calc
        _ = (r.choose i:ℝ)*(A*B*(N^(i+a)*N^(r-i+b))*(H*K)) := by ring
        _ = _ := by rw [hp]
    _ = _ := by
      have hc : (∑ i ∈ Finset.range (r+1), (r.choose i:ℝ)) = (2:ℝ)^r := by
        exact_mod_cast (Nat.sum_range_choose r)
      rw [hc]
      ring

lemma compact_real_derivative_bound (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    {Q : Set E} (hQ : IsCompact Q) (r : ℕ) :
    ∃ C > 0, ∀ i, i ≤ r → ∀ x ∈ Q, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  have hb (i : Fin (r+1)) : ∃ C > 0, ∀ x ∈ Q, ‖iteratedFDeriv ℝ i.val f x‖ ≤ C := by
    obtain ⟨C,hC,hb⟩ := (hQ.image (hf.continuous_iteratedFDeriv
      (by exact_mod_cast (show (i.val:ℕ∞) ≤ ⊤ from le_top)))).isBounded.exists_pos_norm_le
    exact ⟨C,hC,fun x hx ↦ hb _ ⟨x,hx,rfl⟩⟩
  choose c hc hbound using hb
  have hp : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ ↦ (hc i).le)
  refine ⟨1+∑ i, c i,by linarith,?_⟩
  intro i hi x hx
  have hsum := Finset.single_le_sum (fun j _ ↦ (hc j).le)
    (Finset.mem_univ (⟨i,by omega⟩ : Fin (r+1)))
  exact (hbound ⟨i,by omega⟩ x hx).trans (by linarith)

end
end Yau.Geometry

end OAI
