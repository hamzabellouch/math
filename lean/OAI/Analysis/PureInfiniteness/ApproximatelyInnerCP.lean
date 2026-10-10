import OAI.Analysis.PureInfiniteness.RelativeOneStep

namespace OAI

/-! A point-norm limit of finite inner compressions is completely positive.
This gives positivity for the actual finite coefficient cone used in KR02. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder Topology
open Filter

namespace WeakPureInfiniteness

variable {B D : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder D] [StarOrderedRing D]

lemma ApproximatelyInnerAlong.completelyPositive (β : B →⋆ₙₐ[ℂ] D)
    {T : B →L[ℂ] D} (hT : ApproximatelyInnerAlong β T) : CompletelyPositive T := by
  classical
  intro n M hM
  let F : Finset B := Finset.univ.image (fun p : Fin n × Fin n => M p.1 p.2)
  have happ (k : ℕ) : ∃ m : ℕ, ∃ v : Fin m → D, ∀ b ∈ F,
      ‖T b - ∑ j, star (v j) * β b * v j‖ < 1 / ((k : ℝ) + 1) :=
    hT F _ (by positivity)
  choose m v hv using happ
  let Y (k : ℕ) : CStarMatrix (Fin n) (Fin n) D :=
    ∑ j : Fin (m k), star (diagonalCopies n (v k j)) *
      CStarMatrix.mapₙₐ β M * diagonalCopies n (v k j)
  have hY (k : ℕ) : 0 ≤ Y k := by
    apply Finset.sum_nonneg
    intro j _
    exact star_left_conjugate_nonneg (map_nonneg (CStarMatrix.mapₙₐ β) hM) _
  have hentry (k : ℕ) (i j : Fin n) :
      Y k i j = ∑ p : Fin (m k), star (v k p) * β (M i j) * v k p := by
    change matrixEntryLinear i j (Y k) = _
    simp only [Y, map_sum]
    apply Finset.sum_congr rfl
    intro p _
    change (star (diagonalCopies n (v k p)) * CStarMatrix.mapₙₐ β M *
      diagonalCopies n (v k p)) i j = _
    simp [diagonalCopies, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Matrix.diagonal_apply, apply_ite, ite_mul]
  have ht : Tendsto Y atTop (𝓝 (CStarMatrix.ofMatrix (fun i j => T (M i j)))) := by
    change Tendsto (fun k i j => Y k i j) _ (𝓝 (fun i j => T (M i j)))
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hb : ∀ k, ‖Y k i j - T (M i j)‖ ≤ 1 / ((k : ℝ) + 1) := by
      intro k
      rw [hentry, norm_sub_rev]
      exact (hv k _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)).le
    exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (Eventually.of_forall hb) tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto ht (Eventually.of_forall hY)

end WeakPureInfiniteness

end

end OAI
