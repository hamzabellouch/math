import OAI.Analysis.KadisonKastler.FreeDiagonalLetters
import OAI.Analysis.KadisonKastler.FockRelations

namespace OAI

/-! # Constructing creation operators from the leading-word projections -/

namespace KadisonKastler

noncomputable section

section Blocks
variable {A : Type*} [CStarAlgebra A] {p q a b : A}

private theorem offDiagonal_eq
    (h : (1 - p) * q * (1 - p) = 0) : p * q * (1 - p) = q * (1 - p) := by
  have he : p * q * (1 - p) = q * (1 - p) - (1 - p) * q * (1 - p) := by
    noncomm_ring
  rw [he, h, sub_zero]

private theorem offDiagonal_blocks (hp : IsStarProjection p) (hq : IsSelfAdjoint q)
    (h : (1 - p) * q * (1 - p) = 0) :
    q = p * q * (1 - p) + p * q * p + star (p * q * (1 - p)) := by
  have he : q = p * q * (1 - p) + p * q * p + star (p * q * (1 - p)) +
      (1 - p) * q * (1 - p) := by
    rw [star_mul, star_mul, hp.isSelfAdjoint.star_eq, hq.star_eq,
      hp.one_sub.isSelfAdjoint.star_eq]
    noncomm_ring
  simpa only [h, add_zero] using he

private theorem offDiagonal_gram (hp : IsStarProjection p)
    (ha : IsSelfAdjoint a)
    (hca : (1 - p) * a * (1 - p) = 0) (hcb : (1 - p) * b * (1 - p) = 0)
    (s t c : ℂ) (hab : a * b = s • a - t • b + c • 1) :
    star (p * a * (1 - p)) * (p * b * (1 - p)) = c • (1 - p) := by
  rw [offDiagonal_eq hca, offDiagonal_eq hcb, star_mul,
    hp.one_sub.isSelfAdjoint.star_eq, ha.star_eq]
  calc
    (1 - p) * a * (b * (1 - p)) = (1 - p) * (a * b) * (1 - p) := by noncomm_ring
    _ = c • (1 - p) := by
      rw [hab]
      generalize hq : 1 - p = q at hca hcb ⊢
      have hqq : q * q = q := by
        rw [← hq]
        exact hp.one_sub.isIdempotentElem.eq
      simp only [mul_add, mul_sub, mul_smul_comm, add_mul, sub_mul, smul_mul_assoc,
        hca, hcb, smul_zero, sub_self, zero_add, mul_one, hqq]

end Blocks

variable {H ι α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype α] [DecidableEq α] [Nonempty α]

/-- The only geometric construction still needed is a family of orthogonal
leading-word projections whose complementary centered blocks vanish. -/
def freeDiagonalModel_of_leadingProjections
    (e : ι → α → H →L[ℂ] H)
    (he : ∀ i a, IsStarProjection (e i a))
    (heo : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (hes : ∀ i, ∑ a, e i a = 1)
    (P : ι → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (hPo : ∀ i j, i ≠ j → P i * P j = 0)
    (hblock : ∀ i a, (1 - P i) * diagonalCentered e i a * (1 - P i) = 0) :
    FreeDiagonalModel ι α H where
  e := e
  P := P
  C i a := P i * diagonalCentered e i a * (1 - P i)
  e_projection := he
  e_orthogonal := heo
  e_sum := hes
  P_projection := hP
  P_orthogonal := hPo
  creation_range i a := by
    simp only [← mul_assoc, (hP i).isIdempotentElem.eq]
  creation_domain i a := by
    rw [mul_assoc, (hP i).one_sub.isIdempotentElem.eq]
  creation_gram i a b := by
    apply offDiagonal_gram (hP i)
      (show IsSelfAdjoint (diagonalCentered e i a) from star_diagonalCentered e he i a)
      (hblock i a) (hblock i b)
    exact diagonalCentered_mul e he heo i a b
  centered_decomposition i a :=
    offDiagonal_blocks (hP i)
      (show IsSelfAdjoint (diagonalCentered e i a) from star_diagonalCentered e he i a)
      (hblock i a)

end

end KadisonKastler

end OAI
