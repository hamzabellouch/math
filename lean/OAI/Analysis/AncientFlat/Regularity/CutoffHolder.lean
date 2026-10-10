import OAI.Analysis.AncientFlat.Regularity.HolderAlgebra

namespace OAI
noncomputable section
open Set Filter
namespace ParabolicLocalization
open ParabolicInterior
variable {V : Type} {E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma supported_cutoff_holder (α A B N H : ℝ) (Ω S : Set (V × ℝ))
    (χ : V × ℝ → ℝ) (f : V × ℝ → E)
    (hA : 0≤A) (hB : 0≤B) (hN : 0≤N) (hH : 0≤H)
    (hz : ∀ p∈Ω, p∉S → χ p=0)
    (hb : ∀ p∈Ω, ‖χ p‖≤B)
    (hh : ∀ p∈Ω, ∀ q∈Ω, ‖χ p-χ q‖≤A*pdist p q^α)
    (hf : ∀ p∈Ω, p∈S → ‖f p‖≤N)
    (hfh : ∀ p∈Ω, p∈S → ∀ q∈Ω, q∈S → ‖f p-f q‖≤H*pdist p q^α) :
    HolderBound α Ω (fun p => χ p • f p) (B*H+A*N+B*N) := by
  have hBH := mul_nonneg hB hH
  have hAN := mul_nonneg hA hN
  have hBN := mul_nonneg hB hN
  refine ⟨?_,?_⟩
  · intro p hp
    change ‖χ p • f p‖≤_
    by_cases hs : p∈S
    · rw [norm_smul]
      exact (mul_le_mul (hb p hp) (hf p hp hs) (norm_nonneg _) hB).trans (by linarith)
    · rw [hz p hp hs,zero_smul,norm_zero]
      positivity
  · intro p hp q hq
    change ‖χ p • f p-χ q • f q‖≤_
    have hd : 0≤pdist p q^α := Real.rpow_nonneg (pdist_nonneg p q) _
    by_cases hs : p∈S <;> by_cases ht : q∈S
    · rw [show χ p • f p-χ q • f q=χ p • (f p-f q)+(χ p-χ q) • f q by rw [smul_sub,sub_smul]; abel]
      apply (norm_add_le _ _).trans
      simp only [norm_smul]
      have h1 := mul_le_mul (hb p hp) (hfh p hp hs q hq ht) (norm_nonneg _) hB
      have h2 := mul_le_mul (hh p hp q hq) (hf q hq ht) (norm_nonneg _) (mul_nonneg hA hd)
      nlinarith [mul_nonneg hBN hd]
    · rw [hz q hq ht,zero_smul,sub_zero,norm_smul]
      have hc := hh p hp q hq
      rw [hz q hq ht,sub_zero] at hc
      have := mul_le_mul hc (hf p hp hs) (norm_nonneg _) (mul_nonneg hA hd)
      nlinarith [mul_nonneg hBN hd,mul_nonneg hBH hd]
    · rw [hz p hp hs,zero_smul,zero_sub,norm_neg,norm_smul]
      have hc := hh p hp q hq
      rw [hz p hp hs,zero_sub,norm_neg] at hc
      have := mul_le_mul hc (hf q hq ht) (norm_nonneg _) (mul_nonneg hA hd)
      nlinarith [mul_nonneg hBN hd,mul_nonneg hBH hd]
    · rw [hz p hp hs,hz q hq ht,zero_smul,zero_smul,sub_self,norm_zero]
      positivity
end ParabolicLocalization

end

end OAI
