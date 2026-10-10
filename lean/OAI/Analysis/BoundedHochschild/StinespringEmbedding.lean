import OAI.Analysis.BoundedHochschild.StinespringStar

namespace OAI

/-! The bounded vector map and factorization of a completely positive map. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def stinespringPreVector (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    StinespringPreSpace φ := Finsupp.single (1, ξ) 1

def stinespringVector (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    StinespringSpace φ := Completion.coe' (stinespringPreVector φ ξ)

lemma stinespringVector_pairing (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (x : StinespringPreSpace φ) (ξ : H) :
    inner ℂ (x : StinespringSpace φ) (stinespringVector φ ξ) =
      x.sum (fun p z => star z * inner ℂ p.2 (φ (star p.1) ξ)) := by
  classical
  rw [stinespringVector, Completion.inner_coe]
  change kernelForm (stinespringKernel φ) x (stinespringPreVector φ ξ) = _
  simp [kernelForm, stinespringKernel, stinespringPreVector]

lemma stinespringVector_add (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ η : H) :
    stinespringVector φ (ξ + η) = stinespringVector φ ξ + stinespringVector φ η := by
  apply ext_inner_left ℂ
  intro ω
  induction ω using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    simp only [inner_add_right, stinespringVector_pairing, map_add, mul_add,
      Finsupp.sum, Finset.sum_add_distrib]

lemma stinespringVector_smul (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (z : ℂ) (ξ : H) :
    stinespringVector φ (z • ξ) = z • stinespringVector φ ξ := by
  apply ext_inner_left ℂ
  intro ω
  induction ω using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    simp only [inner_smul_right, stinespringVector_pairing, map_smul,
      Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring

lemma stinespringVector_norm_sq (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    ‖stinespringVector φ ξ‖ ^ 2 = (inner ℂ ξ (φ 1 ξ)).re := by
  classical
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ ((stinespringPreVector φ ξ) : StinespringSpace φ) (stinespringVector φ ξ)).re = _
  rw [stinespringVector_pairing]
  simp [stinespringPreVector]

lemma stinespringVector_bound (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    ‖stinespringVector φ ξ‖ ≤ Real.sqrt ‖φ 1‖ * ‖ξ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (norm_nonneg _), stinespringVector_norm_sq]
  calc
    _ ≤ ‖inner ℂ ξ (φ 1 ξ)‖ := Complex.re_le_norm _
    _ ≤ ‖ξ‖ * ‖φ 1 ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖φ 1‖ * ‖ξ‖) :=
      mul_le_mul_of_nonneg_left ((φ 1).le_opNorm ξ) (norm_nonneg _)
    _ = _ := by ring

/-- The bounded map sending a vector to its unit-labelled kernel vector. -/
def stinespringEmbedding (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    H →L[ℂ] StinespringSpace φ :=
  LinearMap.mkContinuous
    { toFun := stinespringVector φ
      map_add' := stinespringVector_add φ
      map_smul' := stinespringVector_smul φ }
    (Real.sqrt ‖φ 1‖) (stinespringVector_bound φ)

@[simp] lemma stinespringEmbedding_apply (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    stinespringEmbedding φ ξ = stinespringVector φ ξ := rfl

lemma stinespringVector_coefficient (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (a : M) (ξ η : H) :
    inner ℂ (stinespringVector φ ξ) (stinespringRepresentation φ a (stinespringVector φ η)) =
      inner ℂ ξ (φ a η) := by
  classical
  change inner ℂ ((stinespringPreVector φ ξ) : StinespringSpace φ)
    (stinespringOperator φ a (stinespringPreVector φ η)) = _
  rw [stinespringOperator_inner_coe]
  simp [kernelForm, stinespringPreVector]

/-- Stinespring factorization on the constructed auxiliary Hilbert space. -/
theorem stinespring_factorization (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : M) :
    φ a = (stinespringEmbedding φ).adjoint.comp
      ((stinespringRepresentation φ a).comp (stinespringEmbedding φ)) := by
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  exact (stinespringVector_coefficient φ a ξ η).symm

end BoundedHochschild.KadisonRingrose

end

end OAI
