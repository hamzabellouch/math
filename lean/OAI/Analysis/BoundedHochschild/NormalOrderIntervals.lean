import OAI.Analysis.BoundedHochschild.PositiveNormalParts

namespace OAI

/-! Compact order intervals of normal positive functionals. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The positive order interval below a fixed positive functional, represented
in the weak dual of the algebra. -/
def weakPositiveOrderInterval (ψ : M →ₚ[ℂ] ℂ) : Set (WeakDual ℂ M) :=
  {F | ∀ a : M, 0 ≤ a → 0 ≤ F a ∧ F a ≤ ψ a}

lemma weakPositiveOrderInterval_norm_bound (ψ : M →ₚ[ℂ] ℂ)
    {F : WeakDual ℂ M} (hF : F ∈ weakPositiveOrderInterval ψ) :
    ‖WeakDual.toStrongDual F‖ ≤ 4 * ‖ψ 1‖ := by
  let G := WeakDual.toStrongDual F
  have hpos (a : M) (ha : 0 ≤ a) : ‖G a‖ ≤ ‖ψ 1‖ * ‖a‖ := by
    exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg (hF a ha).2 (hF a ha).1).trans
      (PositiveLinearMap.norm_apply_le_of_nonneg ψ a ha)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  obtain ⟨x, hx, hxn, ha⟩ := CStarAlgebra.exists_sum_four_nonneg a
  calc
    ‖G a‖ = ‖∑ i : Fin 4, Complex.I ^ (i : ℕ) • G (x i)‖ := by rw [ha, map_sum]; simp
    _ ≤ ∑ i : Fin 4, ‖Complex.I ^ (i : ℕ) • G (x i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 4, ‖G (x i)‖ := by simp only [norm_smul, norm_pow, Complex.norm_I,
      one_pow, one_mul]
    _ ≤ ∑ _i : Fin 4, ‖ψ 1‖ * ‖a‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (hpos (x i) (hx i)).trans (mul_le_mul_of_nonneg_left (hxn i) (norm_nonneg _))
    _ = (4 * ‖ψ 1‖) * ‖a‖ := by simp; ring

omit [StarOrderedRing M] in
lemma weakPositiveOrderInterval_closed (ψ : M →ₚ[ℂ] ℂ) :
    IsClosed (weakPositiveOrderInterval ψ) := by
  change IsClosed {F : WeakDual ℂ M | ∀ a : M, 0 ≤ a → 0 ≤ F a ∧ F a ≤ ψ a}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro a
  apply isClosed_iInter
  intro _ha
  exact (isClosed_le continuous_const (WeakDual.eval_continuous a)).inter
    (isClosed_le (WeakDual.eval_continuous a) continuous_const)

/-- Positive order intervals are weak-star compact by Banach--Alaoglu. -/
theorem weakPositiveOrderInterval_compact (ψ : M →ₚ[ℂ] ℂ) :
    IsCompact (weakPositiveOrderInterval ψ) := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ M) (4 * ‖ψ 1‖)).of_isClosed_subset
    (weakPositiveOrderInterval_closed ψ)
  intro F hF
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using
    weakPositiveOrderInterval_norm_bound ψ hF

/-- If the upper endpoint is normal, every functional in the compact order
interval is normal as well. -/
theorem weakPositiveOrderInterval_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) {F : WeakDual ℂ M}
    (hF : F ∈ weakPositiveOrderInterval ψ) : WeakDual.toStrongDual F ∈ normalDual e := by
  let G := WeakDual.toStrongDual F
  let χ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := G.toLinearMap
      monotone' := (monotone_iff_map_nonneg G.toLinearMap).mpr (fun a ha => (hF a ha).1) }
  exact (mem_normalDual e _).mpr
    (positive_normal_of_dominated e χ ψ hψ (fun a ha => (hF a ha).2))

end KadisonRingrose
end BoundedHochschild

end

end OAI
