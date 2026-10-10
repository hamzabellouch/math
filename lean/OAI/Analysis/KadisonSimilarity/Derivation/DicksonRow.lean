import OAI.Analysis.KadisonSimilarity.Derivation.CStarRowSquare
import OAI.Analysis.KadisonSimilarity.Derivation.HomPolarBound

namespace OAI

/-! Derivation of the norm-two row estimate from the exact little
Grothendieck specialization in Haagerup (1983), Theorem 3.2, as quoted in
Dickson (2014), Lemmas 2.8–2.9, equations (18)–(22). -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Subnormalized states also cover the zero algebra. Only their values on
positive squares and their mass bound are used in the application. -/
def LittleGrothendieckInput (A H : Type*) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Prop :=
  ∀ T : A →L[ℂ] H, ∃ f g : A →ₚ[ℂ] ℂ,
    (f 1).re ≤ 1 ∧ (g 1).re ≤ 1 ∧
    ∀ a, ‖T a‖ ^ 2 ≤ ‖T‖ ^ 2 * ((f (star a * a)).re + (g (a * star a)).re)

def sharpVectorMap (π : BoundedUnitalHom A H) (ξ : H) : A →L[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H ξ).comp
    ⟨(sharpHom π).1.toLinearMap, (sharpHom π).2⟩

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem sharpVectorMap_apply (π : BoundedUnitalHom A H) (ξ : H) (a : A) :
    sharpVectorMap π ξ a = (π.1 (star a)).adjoint ξ := rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem norm_sharpVectorMap_le (π : BoundedUnitalHom A H)
    (hπ : ∀ a, ‖π.1 a‖ ≤ 2 * ‖a‖) (ξ : H) : ‖sharpVectorMap π ξ‖ ≤ 2 * ‖ξ‖ := by
  apply opNorm_le_bound _ (by positivity)
  intro a
  change ‖(sharpHom π).1 a ξ‖ ≤ _
  calc
    _ ≤ ‖(sharpHom π).1 a‖ * ‖ξ‖ := le_opNorm _ _
    _ ≤ (2 * ‖a‖) * ‖ξ‖ := mul_le_mul_of_nonneg_right
      (sharpHom_bound π hπ a) (norm_nonneg ξ)
    _ = (2 * ‖ξ‖) * ‖a‖ := by ring

/-- The polar estimate converts the two-sided square bound into the single
row square, with precisely Dickson's norm-two constant. -/
theorem dickson_vector_states (lg : LittleGrothendieckInput A H)
    (π : BoundedUnitalHom A H) (hπ : ∀ a, ‖π.1 a‖ ≤ 2 * ‖a‖) (ξ : H) :
    ∃ f g : A →ₚ[ℂ] ℂ, (f 1).re ≤ 1 ∧ (g 1).re ≤ 1 ∧
      ∀ a, ‖(π.1 a).adjoint ξ‖ ^ 2 ≤
        16 * ‖ξ‖ ^ 2 * ((f (a * star a)).re + (g (a * star a)).re) := by
  obtain ⟨f, g, hf, hg, hfg⟩ := lg (sharpVectorMap π ξ)
  refine ⟨f, g, hf, hg, ?_⟩
  intro a
  let h := CFC.sqrt (a * star a)
  have hh : 0 ≤ h := CFC.sqrt_nonneg _
  have hsq : h * h = a * star a := CFC.sqrt_mul_sqrt_self _ (mul_star_self_nonneg a)
  have hp := hom_adjoint_sqrt_bound π (by norm_num) hπ a ξ
  change ‖(π.1 a).adjoint ξ‖ ≤ 2 * ‖(π.1 h).adjoint ξ‖ at hp
  have hl := hfg h
  simp only [sharpVectorMap_apply, hh.star_eq, hsq] at hl
  have hpos : 0 ≤ (f (a * star a)).re + (g (a * star a)).re :=
    add_nonneg (f.map_nonneg (mul_star_self_nonneg a)).1
      (g.map_nonneg (mul_star_self_nonneg a)).1
  calc
    _ ≤ (2 * ‖(π.1 h).adjoint ξ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
    _ = 4 * ‖(π.1 h).adjoint ξ‖ ^ 2 := by ring
    _ ≤ 4 * (‖sharpVectorMap π ξ‖ ^ 2 *
        ((f (a * star a)).re + (g (a * star a)).re)) := mul_le_mul_of_nonneg_left hl (by norm_num)
    _ ≤ 4 * ((2 * ‖ξ‖) ^ 2 * ((f (a * star a)).re + (g (a * star a)).re)) := by
      gcongr
      exact norm_sharpVectorMap_le π hπ ξ
    _ = _ := by ring

/-- The summed adjoint-vector bound for one row. -/
theorem dickson_row_adjoint_sum (lg : LittleGrothendieckInput A H)
    (π : BoundedUnitalHom A H) (hπ : ∀ a, ‖π.1 a‖ ≤ 2 * ‖a‖)
    {n : ℕ} (X : Matrix (Fin 1) (Fin n) A) (ξ : H) :
    ∑ j : Fin n, ‖(π.1 (X 0 j)).adjoint ξ‖ ^ 2 ≤
      32 * ‖ξ‖ ^ 2 * ‖CStarMatrix.ofMatrix X‖ ^ 2 := by
  obtain ⟨f, g, hf, hg, hfg⟩ := dickson_vector_states lg π hπ ξ
  calc
    _ ≤ ∑ j : Fin n, 16 * ‖ξ‖ ^ 2 *
        ((f (X 0 j * star (X 0 j))).re + (g (X 0 j * star (X 0 j))).re) :=
      Finset.sum_le_sum (fun j _ => hfg (X 0 j))
    _ = 16 * ‖ξ‖ ^ 2 * ((∑ j : Fin n, (f (X 0 j * star (X 0 j))).re) +
        ∑ j : Fin n, (g (X 0 j * star (X 0 j))).re) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 16 * ‖ξ‖ ^ 2 * (‖CStarMatrix.ofMatrix X‖ ^ 2 + ‖CStarMatrix.ofMatrix X‖ ^ 2) := by
      gcongr
      · exact positiveFunctional_rowSquare_le f hf X
      · exact positiveFunctional_rowSquare_le g hg X
    _ = _ := by ring

/-- The exact row bound, conditional only on the little Grothendieck input. -/
theorem dickson_rowBound_of_littleGrothendieck (lg : LittleGrothendieckInput A H)
    (π : BoundedUnitalHom A H) (hπ : ∀ a, ‖π.1 a‖ ≤ 2 * ‖a‖) :
    RowBound π.1 (4 * Real.sqrt 2) := by
  intro n X
  let R := rectangularMatrixOperator (X.map π.1)
  have hnorm : ‖R.adjoint‖ ≤ (4 * Real.sqrt 2) * ‖CStarMatrix.ofMatrix X‖ := by
    apply opNorm_le_bound _ (by positivity)
    intro η
    have hi (j : Fin n) : R.adjoint η j = (π.1 (X 0 j)).adjoint (η 0) := by
      change (rectangularMatrixOperator (X.map π.1)).adjoint η j = _
      rw [rectangularMatrixOperator_adjoint]
      have he := rectangularMatrixOperator_apply
        (show Matrix (Fin n) (Fin 1) (H →L[ℂ] H) from
          fun i j => ((X.map π.1) j i).adjoint) η j
      simpa using he
    have hs := dickson_row_adjoint_sum lg π hπ X (η 0)
    have hη : ‖η 0‖ ^ 2 = ‖η‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp
    have hsq : (4 * Real.sqrt 2) ^ 2 = (32 : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      ‖R.adjoint η‖ ^ 2 = ∑ j : Fin n, ‖(π.1 (X 0 j)).adjoint (η 0)‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp only [hi]
      _ ≤ 32 * ‖η‖ ^ 2 * ‖CStarMatrix.ofMatrix X‖ ^ 2 := by rwa [hη] at hs
      _ = ((4 * Real.sqrt 2 * ‖CStarMatrix.ofMatrix X‖) * ‖η‖) ^ 2 := by
        rw [mul_pow, mul_pow, hsq]
        ring
  simpa only [adjoint.norm_map] using hnorm

/-- Both halves of the published norm-two estimate follow from the same
little Grothendieck specialization. -/
theorem dicksonTwoBound_of_littleGrothendieck (lg : LittleGrothendieckInput A H) :
    DicksonTwoBound (A := A) H :=
  dicksonTwoBound_of_row (dickson_rowBound_of_littleGrothendieck lg)

end KadisonSimilarity

end

end OAI
