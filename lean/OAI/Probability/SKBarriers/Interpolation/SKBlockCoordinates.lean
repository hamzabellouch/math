import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.AverageMeanVariance

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

def skInteraction (N : ℕ) (i : Fin (Fintype.card (Edge N))) : Finset (Fin N) :=
  let e := (Fintype.equivFin (Edge N)).symm i
  {e.val.1,e.val.2}

theorem spinMonomial_skInteraction (N : ℕ) (i : Fin (Fintype.card (Edge N))) (s : Config N) :
    spinMonomial s (skInteraction N i) =
      spin (s ((Fintype.equivFin (Edge N)).symm i).val.1)*
        spin (s ((Fintype.equivFin (Edge N)).symm i).val.2) := by
  exact Finset.prod_pair (ne_of_lt (((Fintype.equivFin (Edge N)).symm i).property))

theorem uniformAtom_sum (k : ℕ) : (∑ _ : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹) = 1 := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

theorem weighted_complement_sum {I J : Type} [Fintype I] [Fintype J]
    (w : J → ℝ) (hw : ∑ j, w j = 1) (E : I → J → ℝ) :
    (∑ i, (1-∑ j, w j*E i j)) = ∑ j, w j*∑ i, (1-E i j) := by
  calc
    _ = ∑ i, ∑ j, w j*(1-E i j) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hw]
    _ = ∑ j, ∑ i, w j*(1-E i j) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

theorem blockCoefficients_add_split {D N k : ℕ} (a : Fin D → ℝ) (v : Fin (k+1) → ℝ) :
    blockCoefficients (N := N) a v =
      blockCoefficients (fun _ : Fin D => 0) v+blockCoefficients a (fun _ : Fin (k+1) => 0) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [blockCoefficients]
  · simp [blockCoefficients]
end SK.Analytic

end
end

end

end OAI
