import OAI.Analysis.KadisonSimilarity.Derivation.CStarRowSquare
import OAI.Analysis.KadisonSimilarity.Derivation.GrothendieckMatrix

namespace OAI

/-! Row bounds for arbitrary bounded homomorphisms in terms of their operator norms. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
theorem norm_sharpVectorMap_le_general (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖) (ξ : H) : ‖sharpVectorMap π ξ‖ ≤ M * ‖ξ‖ := by
  apply opNorm_le_bound _ (by positivity)
  intro a
  change ‖(sharpHom π).1 a ξ‖ ≤ _
  calc
    _ ≤ ‖(sharpHom π).1 a‖ * ‖ξ‖ := le_opNorm _ _
    _ ≤ (M * ‖a‖) * ‖ξ‖ := mul_le_mul_of_nonneg_right
      (sharpHom_bound π hπ a) (norm_nonneg ξ)
    _ = (M * ‖ξ‖) * ‖a‖ := by ring

/-- The polar estimate converts the two-sided square bound into the single
row square, with a bound depending only on the norm of the homomorphism. -/
theorem boundedHom_vector_states (lg : LittleGrothendieckInput A H)
    (π : BoundedUnitalHom A H) {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖) (ξ : H) :
    ∃ f g : A →ₚ[ℂ] ℂ, (f 1).re ≤ 1 ∧ (g 1).re ≤ 1 ∧
      ∀ a, ‖(π.1 a).adjoint ξ‖ ^ 2 ≤
        M ^ 4 * ‖ξ‖ ^ 2 * ((f (a * star a)).re + (g (a * star a)).re) := by
  obtain ⟨f, g, hf, hg, hfg⟩ := lg (sharpVectorMap π ξ)
  refine ⟨f, g, hf, hg, ?_⟩
  intro a
  let h := CFC.sqrt (a * star a)
  have hh : 0 ≤ h := CFC.sqrt_nonneg _
  have hsq : h * h = a * star a := CFC.sqrt_mul_sqrt_self _ (mul_star_self_nonneg a)
  have hp := hom_adjoint_sqrt_bound π hM hπ a ξ
  change ‖(π.1 a).adjoint ξ‖ ≤ M * ‖(π.1 h).adjoint ξ‖ at hp
  have hl := hfg h
  simp only [sharpVectorMap_apply, hh.star_eq, hsq] at hl
  have hpos : 0 ≤ (f (a * star a)).re + (g (a * star a)).re :=
    add_nonneg (f.map_nonneg (mul_star_self_nonneg a)).1
      (g.map_nonneg (mul_star_self_nonneg a)).1
  calc
    _ ≤ (M * ‖(π.1 h).adjoint ξ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
    _ = M ^ 2 * ‖(π.1 h).adjoint ξ‖ ^ 2 := by ring
    _ ≤ M ^ 2 * (‖sharpVectorMap π ξ‖ ^ 2 *
        ((f (a * star a)).re + (g (a * star a)).re)) := mul_le_mul_of_nonneg_left hl (sq_nonneg M)
    _ ≤ M ^ 2 * ((M * ‖ξ‖) ^ 2 * ((f (a * star a)).re + (g (a * star a)).re)) := by
      gcongr
      exact norm_sharpVectorMap_le_general π hM hπ ξ
    _ = _ := by ring

/-- The summed adjoint-vector bound for one row. -/
theorem boundedHom_row_adjoint_sum (lg : LittleGrothendieckInput A H)
    (π : BoundedUnitalHom A H) {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    {n : ℕ} (X : Matrix (Fin 1) (Fin n) A) (ξ : H) :
    ∑ j : Fin n, ‖(π.1 (X 0 j)).adjoint ξ‖ ^ 2 ≤
      (2 * M ^ 4) * ‖ξ‖ ^ 2 * ‖CStarMatrix.ofMatrix X‖ ^ 2 := by
  obtain ⟨f, g, hf, hg, hfg⟩ := boundedHom_vector_states lg π hM hπ ξ
  calc
    _ ≤ ∑ j : Fin n, M ^ 4 * ‖ξ‖ ^ 2 *
        ((f (X 0 j * star (X 0 j))).re + (g (X 0 j * star (X 0 j))).re) :=
      Finset.sum_le_sum (fun j _ => hfg (X 0 j))
    _ = M ^ 4 * ‖ξ‖ ^ 2 * ((∑ j : Fin n, (f (X 0 j * star (X 0 j))).re) +
        ∑ j : Fin n, (g (X 0 j * star (X 0 j))).re) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ M ^ 4 * ‖ξ‖ ^ 2 * (‖CStarMatrix.ofMatrix X‖ ^ 2 + ‖CStarMatrix.ofMatrix X‖ ^ 2) := by
      gcongr
      · exact positiveFunctional_rowSquare_le f hf X
      · exact positiveFunctional_rowSquare_le g hg X
    _ = _ := by ring

/-- A row bound uniform over finite rows. -/
theorem boundedHom_rowBound (lg : LittleGrothendieckInput A H)
    (π : BoundedUnitalHom A H) {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖) :
    RowBound π.1 (2 * M ^ 2) := by
  intro n X
  let R := rectangularMatrixOperator (X.map π.1)
  have hnorm : ‖R.adjoint‖ ≤ (2 * M ^ 2) * ‖CStarMatrix.ofMatrix X‖ := by
    apply opNorm_le_bound _ (by positivity)
    intro η
    have hi (j : Fin n) : R.adjoint η j = (π.1 (X 0 j)).adjoint (η 0) := by
      change (rectangularMatrixOperator (X.map π.1)).adjoint η j = _
      rw [rectangularMatrixOperator_adjoint]
      have he := rectangularMatrixOperator_apply
        (show Matrix (Fin n) (Fin 1) (H →L[ℂ] H) from
          fun i j => ((X.map π.1) j i).adjoint) η j
      simpa using he
    have hs := boundedHom_row_adjoint_sum lg π hM hπ X (η 0)
    have hη : ‖η 0‖ ^ 2 = ‖η‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp
    have hsq : (2 * M ^ 2) ^ 2 = 4 * M ^ 4 := by ring
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      ‖R.adjoint η‖ ^ 2 = ∑ j : Fin n, ‖(π.1 (X 0 j)).adjoint (η 0)‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp only [hi]
      _ ≤ (2 * M ^ 4) * ‖η‖ ^ 2 * ‖CStarMatrix.ofMatrix X‖ ^ 2 := by rwa [hη] at hs
      _ ≤ ((2 * M ^ 2 * ‖CStarMatrix.ofMatrix X‖) * ‖η‖) ^ 2 := by
        rw [mul_pow, mul_pow, hsq]
        nlinarith [sq_nonneg ‖η‖, sq_nonneg ‖CStarMatrix.ofMatrix X‖,
          mul_nonneg (pow_nonneg hM 4) (mul_nonneg (sq_nonneg ‖η‖) (sq_nonneg ‖CStarMatrix.ofMatrix X‖))]
  simpa only [adjoint.norm_map] using hnorm


end KadisonSimilarity

end

end OAI
