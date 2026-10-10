import OAI.Geometry.NodalSets.Elliptic.FrequencyLeibniz

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma frequency_product_derivative_on (f g : E → ℝ) {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g U) (x : E) (hx : x ∈ U) (r a b : ℕ) {N A B H K : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (_ : 0 ≤ B) (hH : 0 ≤ H) (_ : 0 ≤ K)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(i+a)*H)
    (hgb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i g x‖ ≤ B*N^(i+b)*K) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*g y) x‖ ≤
      (2:ℝ)^r*A*B*N^(r+a+b)*(H*K) := by
  have hprod := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx
    (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU hx] at hprod
  refine hprod.trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (r+1), (r.choose i:ℝ)*(A*N^(i+a)*H)*
        (B*N^(r-i+b)*K) := by
      apply Finset.sum_le_sum
      intro i hi
      have hir : i ≤ r := by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      gcongr
      · exact hfb i hir
      · exact hgb (r-i) (by omega)
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

lemma scaled_frequency_product_on (f g : E → ℝ) {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (x : E) (hx : x ∈ U)
    (r s a b : ℕ) {N A B H K : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(s*i+a)*H)
    (hgb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i g x‖ ≤ B*N^(s*i+b)*K) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*g y) x‖ ≤
      (2:ℝ)^r*A*B*N^(s*r+a+b)*(H*K) := by
  have hf' (i : ℕ) (hi : i ≤ r) :
      ‖iteratedFDeriv ℝ i f x‖ ≤ (A*N^a)*(N^s)^(i+0)*H := by
    convert hfb i hi using 1
    simp only [Nat.add_zero,pow_add,← pow_mul]
    ring
  have hg' (i : ℕ) (hi : i ≤ r) :
      ‖iteratedFDeriv ℝ i g x‖ ≤ (B*N^b)*(N^s)^(i+0)*K := by
    convert hgb i hi using 1
    simp only [Nat.add_zero,pow_add,← pow_mul]
    ring
  have h := frequency_product_derivative_on f g hU hf hg x hx r 0 0
    (by positivity) (by positivity) (by positivity) hH hK hf' hg'
  convert h using 1
  simp only [Nat.add_zero,pow_add,← pow_mul]
  ring

end
end Yau.Geometry

end OAI
