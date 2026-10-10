import OAI.NumberTheory.TotientAsymptotic.SquareRemainderLayer
import OAI.NumberTheory.TotientAsymptotic.NormalInternalDiscard

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma finite_square_case_sum {β : Type*} (Q I : Finset ℕ)
    (S : ℕ → ℕ → ℕ → Finset β) (f : β → ℝ) (hf : ∀ y, 0 ≤ f y)
    {C A E h z : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hI : (I.card : ℝ) ≤ h) (hz : 1 ≤ z) (hQ : ∀ q ∈ Q, z < (q : ℝ))
    (hS : ∀ q ∈ Q, ∀ j ∈ I, ∀ k ∈ I,
      (∑ y ∈ S q j k, f y) ≤ C*A*E*((q : ℝ)^2)⁻¹) :
    (∑ y ∈ Q.biUnion (fun q => I.biUnion (fun j => I.biUnion (S q j))), f y) ≤
      C*(h^2*A*E)*(2/z) := by
  classical
  have hi0 : 0 ≤ h := (Nat.cast_nonneg I.card).trans hI
  have hqsum := inverse_square_tail Q hz hQ
  have hcases (q : ℕ) (hq : q ∈ Q) :
      (∑ y ∈ I.biUnion (fun j => I.biUnion (S q j)), f y) ≤
      C*(h^2*A*E)*((q : ℝ)^2)⁻¹ := by
    calc
      _ ≤ ∑ j ∈ I, ∑ k ∈ I, ∑ y ∈ S q j k, f y := by
        apply (nonnegative_sum_biUnion_le _ _ _ hf).trans
        exact Finset.sum_le_sum (fun j _ => nonnegative_sum_biUnion_le _ _ _ hf)
      _ ≤ ∑ _j ∈ I, ∑ _k ∈ I, C*A*E*((q : ℝ)^2)⁻¹ :=
        Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => hS q hq j hj k hk))
      _ = C*((I.card : ℝ)^2*A*E)*((q : ℝ)^2)⁻¹ := by simp; ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ q ∈ Q, ∑ y ∈ I.biUnion (fun j => I.biUnion (S q j)), f y :=
      nonnegative_sum_biUnion_le _ _ _ hf
    _ ≤ ∑ q ∈ Q, C*(h^2*A*E)*((q : ℝ)^2)⁻¹ := Finset.sum_le_sum hcases
    _ = C*(h^2*A*E)*(∑ q ∈ Q, ((q : ℝ)^2)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hqsum (by positivity)

lemma discard_square_log_mass {b : ℝ} (hb : 2 ≤ b) :
    2*(1+Real.log (discardPrimeBound b : ℝ))^2 ≤ (8*Real.exp 2)*Real.exp (4*b) := by
  have hn := discardPrimeBound_bounds hb
  have hn1 : (1 : ℝ) < discardPrimeBound b := by exact_mod_cast (show 1 < discardPrimeBound b by omega)
  have hl : Real.log (discardPrimeBound b : ℝ) ≤ Real.exp (2*b+1) := by
    simpa only [B,Real.exp_log (Real.log_pos hn1)] using Real.exp_le_exp.mpr hn.2.2.1
  have he1 : 1 ≤ Real.exp (2*b+1) := Real.one_le_exp (by linarith)
  have hA : 0 ≤ 1+Real.log (discardPrimeBound b : ℝ) := by
    linarith [Real.log_nonneg hn1.le]
  have hAb : 1+Real.log (discardPrimeBound b : ℝ) ≤ 2*Real.exp (2*b+1) := by linarith
  have hs := pow_le_pow_left₀ hA hAb 2
  have he : (Real.exp (2*b+1))^2=Real.exp (4*b+2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [mul_pow,he,Real.exp_add] at hs
  nlinarith

end TotientAsymptotic

end

end OAI
