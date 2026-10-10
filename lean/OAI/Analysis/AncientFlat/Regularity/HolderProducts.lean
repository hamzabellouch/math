import OAI.Analysis.AncientFlat.Regularity.HolderAlgebra

namespace OAI
noncomputable section
open Set Filter
namespace ParabolicInterior
variable {V : Type} [NormedAddCommGroup V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [NormedSpace ℝ E] in
lemma HolderBound.neg {α K : ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → E}
    (hf : HolderBound α Ω f K) : HolderBound α Ω (fun p => -f p) K := by
  constructor
  · intro p hp; simpa only [norm_neg] using hf.1 p hp
  · intro p hp q hq; simpa only [neg_sub_neg,norm_sub_rev] using hf.2 p hp q hq
lemma scalar_product_separated (α A B N H : ℝ) (Ω : Set (V × ℝ))
    (a : V × ℝ → ℝ) (g : V × ℝ → E)
    (hA : 0≤A) (hB : 0≤B) (hN : 0≤N) (hH : 0≤H)
    (ha : ∀ p∈Ω, ‖a p‖≤A) (hah : ∀ p∈Ω, ∀ q∈Ω, ‖a p-a q‖≤B*pdist p q^α)
    (hg : ∀ p∈Ω, ‖g p‖≤N) (hgh : ∀ p∈Ω, ∀ q∈Ω, ‖g p-g q‖≤H*pdist p q^α) :
    HolderBound α Ω (fun p => a p • g p) (A*H+B*N+A*N) := by
  have hh := supported_freezing_error α A B H N Ω univ a g hA hB hH hN
    (fun p _ hp => False.elim (hp (mem_univ p))) (fun p hp _ => ha p hp)
    (fun p hp _ q hq _ => hah p hp q hq) hg hgh
  simpa only [mem_univ,ite_true] using hh
lemma HolderBound.mul {α A B : ℝ} {Ω : Set (V × ℝ)} {f g : V × ℝ → ℂ}
    (hf : HolderBound α Ω f A) (hg : HolderBound α Ω g B) (hA : 0≤A) (hB : 0≤B) :
    HolderBound α Ω (fun p => f p*g p) (2*A*B) := by
  refine ⟨?_,?_⟩
  · intro p hp
    rw [norm_mul]
    exact (mul_le_mul (hf.1 p hp) (hg.1 p hp) (norm_nonneg _) hA).trans (by nlinarith [mul_nonneg hA hB])
  · intro p hp q hq
    rw [show f p*g p-f q*g q=f p*(g p-g q)+(f p-f q)*g q by ring]
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    have h1 := mul_le_mul (hf.1 p hp) (hg.2 p hp q hq) (norm_nonneg _) hA
    have h2 := mul_le_mul (hf.2 p hp q hq) (hg.1 q hq) (norm_nonneg _) (mul_nonneg hA (Real.rpow_nonneg (pdist_nonneg p q) _))
    nlinarith
lemma HolderBound.const_smul {α K : ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → E}
    (hf : HolderBound α Ω f K) (c : ℝ) :
    HolderBound α Ω (fun p => c • f p) (|c| *K) := by
  refine ⟨fun p hp => ?_,fun p hp q hq => ?_⟩
  · rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf.1 p hp) (abs_nonneg c)
  · rw [← smul_sub,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hf.2 p hp q hq) (abs_nonneg c)).trans_eq (by ring)
end ParabolicInterior

end

end OAI
