import OAI.Analysis.KadisonKastler.RowEnergy
import OAI.Analysis.KadisonKastler.ProjectionModuleMaps

namespace OAI

/-! Equality in row contraction detects the right-module identities. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem normalizedRow_no_loss {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (hr : ∑ i, r i * star (r i) = 1) (v : ι → H)
    (he : (∑ i, ‖v i‖ ^ 2) = ‖rowSynthesis r v‖ ^ 2) (i : ι) :
    v i = (star (r i) : H →L[ℂ] H) (rowSynthesis r v) := by
  have hz := normalizedRow_variance r hr v
  rw [he, sub_self] at hz
  have hle : ‖v i - (star (r i) : H →L[ℂ] H) (rowSynthesis r v)‖ ^ 2 ≤
      ∑ j, ‖v j - (star (r j) : H →L[ℂ] H) (rowSynthesis r v)‖ ^ 2 :=
    Finset.single_le_sum (fun j _ =>
      sq_nonneg ‖v j - (star (r j) : H →L[ℂ] H) (rowSynthesis r v)‖) (Finset.mem_univ i)
  rw [hz] at hle
  have hsq : ‖v i - (star (r i) : H →L[ℂ] H) (rowSynthesis r v)‖ ^ 2 = 0 :=
    le_antisymm hle (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))

theorem finiteRightAverage_no_loss {M : VonNeumannAlgebra H}
    {ι : Type*} [Fintype ι] (r : ι → Algebra M)
    (hr : ∑ i, r i * star (r i) = 1)
    (F : Algebra M →ₗ[ℂ] Algebra M) (a : Algebra M) (ξ : H)
    (he : rowEnergy F (fun i => a * r i) ξ =
      ‖(star (finiteRightAverage r F a) : H →L[ℂ] H) ξ‖ ^ 2) (i : ι) :
    (star (F (a * r i)) : H →L[ℂ] H) ξ =
      (star (r i) : H →L[ℂ] H)
        ((star (finiteRightAverage r F a) : H →L[ℂ] H) ξ) := by
  rw [finiteRightAverage_star_apply] at he ⊢
  exact normalizedRow_no_loss r hr _ he i

end

end KadisonKastler

end OAI
