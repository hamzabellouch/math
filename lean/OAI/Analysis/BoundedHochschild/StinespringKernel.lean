import OAI.Analysis.BoundedHochschild.PositiveKernelSpace

namespace OAI

/-! The positive scalar kernel of an operator-valued completely positive map.
No normality or separability assumption is required. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma completelyPositive_star (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : M) :
    φ (star a) = star (φ a) := by
  obtain ⟨x, hx, _, rfl⟩ := CStarAlgebra.exists_sum_four_nonneg a
  have hxstar (i : Fin 4) : star (x i) = x i := (IsSelfAdjoint.of_nonneg (hx i)).star_eq
  have hystar (i : Fin 4) : star (φ (x i)) = φ (x i) :=
    (IsSelfAdjoint.of_nonneg (map_nonneg φ (hx i))).star_eq
  simp only [star_sum, star_smul, map_sum, map_smul, hxstar, hystar]

/-- The coefficient kernel on formal algebra-vector pairs. -/
def stinespringKernel (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    Matrix (M × H) (M × H) ℂ :=
  fun p q => inner ℂ p.2 (φ (star p.1 * q.1) q.2)

lemma stinespringKernel_hermitian (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    (stinespringKernel φ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  change star (inner ℂ q.2 (φ (star q.1 * p.1) p.2)) =
    inner ℂ p.2 (φ (star p.1 * q.1) q.2)
  rw [← starRingEnd_apply, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right]
  rw [← ContinuousLinearMap.star_eq_adjoint, ← completelyPositive_star]
  simp only [star_mul, star_star]

lemma kernelForm_coefficients {J : Type*}
    (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : J → M) (ξ : J → H) (x : J →₀ ℂ) :
    kernelForm (fun i j => inner ℂ (ξ i) (φ (star (a i) * a j) (ξ j))) x x =
      ∑ i : x.support, ∑ j : x.support,
        inner ℂ (x i • ξ i) (φ (star (a i) * a j) (x j • ξ j)) := by
  classical
  unfold kernelForm
  rw [Finsupp.sum, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finsupp.sum, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [inner_smul_left, map_smul, inner_smul_right, starRingEnd_apply]
  ring

/-- Complete positivity makes all finite formal-vector norms nonnegative
in this construction. -/
theorem stinespringKernel_positive (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    (stinespringKernel φ).PosSemidef := by
  classical
  refine ⟨stinespringKernel_hermitian φ, ?_⟩
  intro x
  change 0 ≤ kernelForm (fun p q : M × H =>
    inner ℂ p.2 (φ (star p.1 * q.1) q.2)) x x
  rw [kernelForm_coefficients]
  exact completelyPositive_kernel_nonneg φ
    (fun i : x.support => i.val.1) (fun i : x.support => x i • i.val.2)

/-- The auxiliary Hilbert space of a completely positive map. -/
abbrev StinespringSpace (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :=
  PositiveKernelHilbert (stinespringKernel φ) (stinespringKernel_positive φ)

end BoundedHochschild.KadisonRingrose

end

end OAI
