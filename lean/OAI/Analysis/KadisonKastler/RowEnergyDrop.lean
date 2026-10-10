import OAI.Analysis.KadisonKastler.RowEnergy

namespace OAI

/-! A quantitative defect forces a definite loss of row energy. -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rowEnergy_drop_bound {M : VonNeumannAlgebra H}
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : Algebra M →ₗ[ℂ] Algebra M) (r : ι → Algebra M) (s : κ → Algebra M)
    (hs : ∑ j, s j * star (s j) = 1) (ξ : H) (i : ι) (j : κ) :
    rowEnergy (finiteRightAverage s F) r ξ +
      ‖(star (F (r i * s j)) : H →L[ℂ] H) ξ - (star (s j) : H →L[ℂ] H)
        ((star (finiteRightAverage s F (r i)) : H →L[ℂ] H) ξ)‖ ^ 2 ≤
      rowEnergy F (fun ij : ι × κ => r ij.1 * s ij.2) ξ := by
  let v := fun i j => ‖(star (F (r i * s j)) : H →L[ℂ] H) ξ -
    (star (s j) : H →L[ℂ] H)
      ((star (finiteRightAverage s F (r i)) : H →L[ℂ] H) ξ)‖ ^ 2
  have hj : v i j ≤ ∑ k, v i k :=
    Finset.single_le_sum (fun k _ => show 0 ≤ v i k from sq_nonneg _) (Finset.mem_univ j)
  have hi : (∑ k, v i k) ≤ ∑ l, ∑ k, v l k :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ =>
      show 0 ≤ v l k from sq_nonneg _)
      (Finset.mem_univ i)
  have h := hj.trans hi
  have he := rowEnergy_rightAverage_variance F r s hs ξ
  change _ = ∑ l, ∑ k, v l k at he
  change _ + v i j ≤ _
  linarith

end

end KadisonKastler

end OAI
