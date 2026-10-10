import OAI.RepresentationTheory.FoulkesHowe.DerivationInjectivity
import OAI.RepresentationTheory.FoulkesHowe.BlockDerivation
import OAI.RepresentationTheory.FoulkesHowe.BlockWeight
import OAI.RepresentationTheory.FoulkesHowe.ShiftHomogeneity

namespace OAI

noncomputable section

namespace Problem346

open MvPolynomial PolynomialWeights

variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq B]

/-- Positive-weight injectivity for the shared `blockShift` derivation API. -/
theorem blockShift_eq_zero_of_pos_weight (src dst : B) (hsd : src ≠ dst)
    {f : MvPolynomial (B × I) ℂ} {p q : ℕ} (hpq : q < p)
    (hp : IsBlockHomogeneous src f p) (hq : IsBlockHomogeneous dst f q)
    (hDf : blockShift ℂ src dst f = 0) : f = 0 := by
  refine derivation_eq_zero_of_positive_weight
    (blockShift ℂ src dst) (blockShift ℂ dst src)
    (blockShift ℂ src src - blockShift ℂ dst dst)
    (blockShift_commutator ℂ src dst) (blockShift_weight_commutator ℂ src dst hsd)
    ?_ f p q hpq ?_ hDf
  · rintro ⟨b, i⟩
    exact blockShift_square_X ℂ dst src b hsd.symm i
  · apply block_difference_eigenvalue src dst _ _ _ _ hp hq
    · intro b i
      by_cases hb : b = src
      · subst b; simp only [blockShift_X]
      · simp only [blockShift_X, ite_eq_right hb]
    · intro b i
      by_cases hb : b = dst
      · subst b; simp only [blockShift_X]
      · simp only [blockShift_X, ite_eq_right hb]

/-- A chain of repeated shifts can be cancelled as long as its least intermediate
source-minus-destination weight is positive. The convenient sufficient bound
`q + 2*n ≤ p` is exactly what is used for each block in the quadratic argument. -/
theorem blockShift_pow_eq_zero_of_degree_bound (src dst : B) (hsd : src ≠ dst)
    {f : MvPolynomial (B × I) ℂ} {p q : ℕ}
    (hp : IsBlockHomogeneous src f p) (hq : IsBlockHomogeneous dst f q)
    (n : ℕ) : q + 2 * n ≤ p →
    (((blockShift ℂ src dst).toLinearMap ^ n) f = 0) → f = 0 := by
  induction n with
  | zero =>
    intro _ hz
    simpa using hz
  | succ n ih =>
    intro hbound hz
    apply ih (by omega)
    apply blockShift_eq_zero_of_pos_weight src dst hsd (p := p - n) (q := q + n)
      (by omega)
    · exact blockShift_pow_source_homogeneous src dst hsd hp n
    · exact blockShift_pow_destination_homogeneous src dst hsd hq n
    · change (blockShift ℂ src dst).toLinearMap
        (((blockShift ℂ src dst).toLinearMap ^ n) f) = 0
      simpa only [pow_succ', Module.End.mul_apply] using hz

end Problem346

end

end OAI
