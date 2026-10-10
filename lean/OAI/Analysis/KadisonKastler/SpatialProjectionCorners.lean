import OAI.Analysis.KadisonKastler.MinimalResidualFamily
import OAI.Analysis.KadisonKastler.TypeIIIProjectionCoordinates

namespace OAI

/-! # Spatial derivations and off-diagonal projection corners -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem boundedSpatialResiduals_preserves_commutant (M : VonNeumannAlgebra H)
    (T X : H →L[ℂ] H) (r : ℝ) (hX : X ∈ M)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (C : H →L[ℂ] H) (hC : C ∈ boundedSpatialResiduals M T X r)
    (w : H →L[ℂ] H) (hw : w ∈ M.commutant) :
    C * w - w * C ∈ M.commutant := by
  have hXw := VonNeumannAlgebra.mem_commutant_iff.mp hw X hX
  have hTc := commutator_mem_commutant_of_preserves M T hT w hw
  let Z := X - C - T
  have hZ : Z ∈ M.commutant := hC.2.2.2
  have he : C * w - w * C = -(T * w - w * T) - (Z * w - w * Z) := by
    dsimp [Z]
    simp only [sub_mul, mul_sub, hXw]
    abel
  rw [he]
  exact M.commutant.sub_mem (M.commutant.neg_mem hTc)
    (M.commutant.sub_mem (M.commutant.mul_mem hZ hw) (M.commutant.mul_mem hw hZ))

theorem CuntzFamily.offDiagonal_mem_of_preserves (S : CuntzFamily (Fin 2) H)
    (N : VonNeumannAlgebra H) (hS : ∀ i, S.entry i ∈ N)
    (C : H →L[ℂ] H) (hC : ∀ a ∈ N, C * a - a * C ∈ N)
    (i j : Fin 2) (hij : i ≠ j) : S.matrix C i j ∈ N := by
  have hm := N.mul_mem (N.toStarSubalgebra.star_mem' (hS i)) (hC (S.entry j) (hS j))
  change star (S.entry i) * C * S.entry j ∈ N.toSubalgebra
  simpa only [mul_sub, ← mul_assoc, S.orthogonal, ite_eq_right hij, zero_mul, sub_zero]
    using hm

theorem CuntzFamily.firstRange_commutes_of_corner_zero (S : CuntzFamily (Fin 2) H)
    (C : H →L[ℂ] H) (hC : IsSelfAdjoint C) (hc : S.matrix C 0 1 = 0) :
    Commute (S.entry 0 * star (S.entry 0)) C := by
  let p := S.entry 0 * star (S.entry 0)
  let q := S.entry 1 * star (S.entry 1)
  have hsum : p + q = 1 := by simpa only [Fin.sum_univ_two] using S.total
  have hpq : p * C * q = 0 := by
    calc
      p * C * q = S.entry 0 * (S.matrix C 0 1) * star (S.entry 1) := by
        simp only [p, q, matrix, mul_assoc]
      _ = 0 := by rw [hc, mul_zero, zero_mul]
  have hqp : q * C * p = 0 := by
    simpa only [star_mul, star_star, hC.star_eq, star_zero, p, q, mul_assoc]
      using congrArg star hpq
  show p * C = C * p
  calc
    p * C = p * C * (p + q) := by rw [hsum, mul_one]
    _ = p * C * p := by rw [mul_add, hpq, add_zero]
    _ = (p + q) * C * p := by rw [add_mul, add_mul, hqp, add_zero]
    _ = C * p := by rw [hsum, one_mul]

end

end KadisonKastler

end OAI
