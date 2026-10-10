import Mathlib
import OAI.Probability.SKGap.Localization.BilinearUnion

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma frobenius_le_card_bound {M : Matrix κ κ ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hM : ∀ i k,|M i k| ≤ ε) : ‖M‖ ≤ (Fintype.card κ:ℝ)*ε := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ ∑ _i : κ,∑ _k : κ, ε^2 := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      rw [Real.norm_eq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hε).mpr (hM i k)
    _ = _ := by simp; ring

def extendColumns (p : κ → ι → ℝ) (N : ι → ℝ) : Matrix ι (κ ⊕ Unit) ℝ :=
  fun i k => Sum.elim (fun r => p r i) (fun _ => N i) k

omit [Fintype κ] in
lemma gram_entry (G : Matrix ι ι ℝ) (V : Matrix ι κ ℝ) (r s : κ) :
    (Vᵀ*G*V) r s=matrixPair G (fun i => V i r) (fun i => V i s) := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,matrixPair,Matrix.mulVec, dotProduct,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _
  ring

theorem augmented_gram_error [DecidableEq ι] [DecidableEq κ] {G W : Matrix ι ι ℝ}
    (hG : Gᵀ=G) (hW : Wᵀ=W) (A : Matrix ι ι ℝ) {B ε : ℝ}
    (hB : 0 < B) (hε : 0 ≤ ε) (p : κ → ι → ℝ) (u : ι → ℝ) (hu : u⬝ᵥu=1)
    (h00 : ∀ r s,|matrixPair (G-A) (p r) (p s)| ≤ ε)
    (h0u : ∀ r,|matrixPair (G-A) (p r) u| ≤ ε)
    (h1u : ∀ r,|matrixPair (G*W-B • A) (p r) u| ≤ ε)
    (h0 : |matrixPair (G-A) u u| ≤ ε)
    (h1 : |matrixPair (G*W-B • A) u u| ≤ ε)
    (h2 : |matrixPair (W*G*W-B • 1-B^2 • A) u u| ≤ ε) :
    let V := extendColumns p (residualGramVector B W u)
    ‖Vᵀ*G*V-fromBlocks (fun r s => matrixPair A (p r) (p s)) 0 0 (1 : Matrix Unit Unit ℝ)‖ ≤
      ((Fintype.card κ:ℝ)+1)*
        (ε+(sqrt B)⁻¹*(1+B)*ε+B⁻¹*(1+2*B+B^2)*ε) := by
  dsimp only
  have hx (r : κ) := centered_gram_mixed_bound G W A hB (p r) u (h0u r) (h1u r)
  have hn := centered_gram_diagonal_bound hG hW A hB u hu h0 h1 h2
  let e₁ := (sqrt B)⁻¹*(1+B)*ε
  let e₂ := B⁻¹*(1+2*B+B^2)*ε
  have he₁ : 0 ≤ e₁ := by dsimp [e₁]; positivity
  have he₂ : 0 ≤ e₂ := by dsimp [e₂]; positivity
  have hεle : ε ≤ ε+e₁+e₂ := (le_add_of_nonneg_right he₁).trans (le_add_of_nonneg_right he₂)
  have he₁le : e₁ ≤ ε+e₁+e₂ := (le_add_of_nonneg_left hε).trans (le_add_of_nonneg_right he₂)
  have he₂le : e₂ ≤ ε+e₁+e₂ := le_add_of_nonneg_left (add_nonneg hε he₁)
  have hall : ∀ r s : κ ⊕ Unit,
      |((extendColumns p (residualGramVector B W u))ᵀ*G*extendColumns p (residualGramVector B W u)-
        fromBlocks (fun r s => matrixPair A (p r) (p s)) 0 0 (1 : Matrix Unit Unit ℝ)) r s| ≤ ε+e₁+e₂ := by
    intro r s
    rw [Matrix.sub_apply,gram_entry]
    cases r with
    | inl r => cases s with
      | inl s =>
        change |matrixPair G (p r) (p s)-matrixPair A (p r) (p s)| ≤ ε+e₁+e₂
        rw [← matrixPair_sub]
        exact (h00 r s).trans hεle
      | inr s =>
        change |matrixPair G (p r) (residualGramVector B W u)-0| ≤ ε+e₁+e₂
        rw [sub_zero]
        exact (hx r).trans he₁le
    | inr r => cases s with
      | inl s =>
        change |matrixPair G (residualGramVector B W u) (p s)-0| ≤ ε+e₁+e₂
        rw [sub_zero,matrixPair_symm hG]
        exact (hx s).trans he₁le
      | inr s =>
        cases r; cases s
        change |matrixPair G (residualGramVector B W u) (residualGramVector B W u)-1| ≤ ε+e₁+e₂
        exact hn.trans he₂le
  convert frobenius_le_card_bound (by positivity : 0 ≤ ε+e₁+e₂) hall using 1
  simp only [Fintype.card_sum,Fintype.card_unique,Nat.cast_add,Nat.cast_one,e₁,e₂]
end SKGap
end
end

end OAI
