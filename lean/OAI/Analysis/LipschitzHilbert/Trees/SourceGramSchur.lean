import OAI.Analysis.LipschitzHilbert.Trees.SourcePlanarPlancherel
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! The elementary Schur estimate for a sparse Gram matrix. It is used
for neighboring labels and comparable scales of actual packet sums. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem symmetric_matrix_energy {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (G : ι → ι → ℝ) (C : ℝ)
    (hG : ∀ i j, 0≤G i j) (hsym : ∀ i j, G i j=G j i)
    (hrow : ∀ i, ∑ j, G i j≤C) :
    (∑ i, ∑ j, G i j*a i*a j)≤C*∑ i, (a i)^2 := by
  have hp (i j : ι) : G i j*a i*a j≤(G i j*(a i)^2+G i j*(a j)^2)/2 := by
    have h := mul_nonneg (hG i j) (sq_nonneg (a i-a j))
    nlinarith only [h]
  have hcol (j : ι) : (∑ i, G i j)≤C := by simpa only [hsym] using hrow j
  calc
    _ ≤ ∑ i, ∑ j, (G i j*(a i)^2+G i j*(a j)^2)/2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = ((∑ i, (∑ j, G i j)*(a i)^2)+(∑ j, (∑ i, G i j)*(a j)^2))/2 := by
      simp only [←Finset.sum_div,Finset.sum_add_distrib,Finset.sum_mul]
      rw [Finset.sum_comm (f := fun i j => G i j*(a j)^2)]
    _ ≤ ((∑ i, C*(a i)^2)+(∑ j, C*(a j)^2))/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact add_le_add (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)))
        (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)))
    _ = _ := by rw [←Finset.mul_sum]; ring

theorem sparse_gram_energy {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ι → E) (near : ι → ι → Prop) (C : ℝ)
    (hsym : ∀ i j, near i j ↔ near j i)
    (hrow : ∀ i, ((Finset.univ.filter fun j => near i j).card:ℝ)≤C)
    (hortho : ∀ i j, ¬near i j → inner ℂ (v i) (v j)=0) :
    ‖∑ i, v i‖^2≤C*∑ i, ‖v i‖^2 := by
  let G := fun i j => if near i j then (1:ℝ) else 0
  have hG : ∀ i j, 0≤G i j := by intro i j; dsimp [G]; split_ifs <;> norm_num
  have hsymG : ∀ i j, G i j=G j i := by intro i j; simp only [G,hsym i j]
  have hrowG : ∀ i, ∑ j, G i j≤C := by
    intro i
    simpa only [G,Finset.sum_boole] using hrow i
  have hentry (i j : ι) : (inner ℂ (v i) (v j)).re≤G i j*‖v i‖*‖v j‖ := by
    by_cases hn : near i j
    · simpa only [G,ite_eq_left hn,one_mul] using (Complex.re_le_norm (inner ℂ (v i) (v j))).trans (norm_inner_le_norm (𝕜 := ℂ) (v i) (v j))
    · simp only [hortho i j hn,Complex.zero_re,G,ite_eq_right hn,zero_mul,le_refl]
  calc
    _ = ∑ i, ∑ j, (inner ℂ (v i) (v j)).re := by
      rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ E]
      simp only [sum_inner,inner_sum,map_sum]
      exact Finset.sum_comm
    _ ≤ ∑ i, ∑ j, G i j*‖v i‖*‖v j‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hentry i j))
    _ ≤ _ := symmetric_matrix_energy (fun i => ‖v i‖) G C hG hsymG hrowG

end LipschitzHilbert

end

end OAI
