import OAI.NumberTheory.SiegelZeros.Determinants.GeneratedGreedyDivisibility

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W37

open scoped NumberField BigOperators
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

omit [CharZero K] in
theorem adjoin_thetaField_eq (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) (n : Fin 4 → ℕ) :
    thetaField (adjoinIntegralGenerators a b d ha hb) n =
      WeightedTorusJets.W34.theta (W36.rootA a b) (W36.rootB a b) n := by
  apply Subtype.ext
  simp [thetaField, Fin.sum_univ_succ, adjoinIntegralGenerators,
    SiegelZeros.W10.adjoinGenerators, SiegelZeros.W10.generators,
    WeightedTorusJets.W34.theta, W36.rootA, W36.rootB]
  ring

theorem rowIntegral_eq_concreteThetaMatrix {m : ℕ}
    (a b : K) (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (orders : Fin m → Fin 3 → ℕ) (columns : Fin m → Fin 4 → ℕ)
    (i j : Fin m) :
    (rowIntegral (adjoinIntegralGenerators a b d ha hb)
      (actualSigma a b d hd hd1 hd2 ha hb) (actualSigmaTau a b d hd hd1 hd2 ha hb)
      (orders i) (columns j) : SiegelZeros.W10.rootField a b) =
      W36.concreteThetaMatrix a b d hd hd1 hd2 ha hb orders columns i j := by
  rw [coe_rowIntegral]
  simp only [rowField, adjoin_thetaField_eq, W36.concreteThetaMatrix,
    W36.thetaRowMatrix, W36.concreteDirections, actualSigma, actualSigmaTau,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, RingHom.id_apply]
  rfl

theorem deltaIntegral_eq_concreteThetaMatrix_det {m : ℕ}
    (a b : K) (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (orders : Fin m → Fin 3 → ℕ) (columns : Fin m → Fin 4 → ℕ) :
    (deltaIntegral (adjoinIntegralGenerators a b d ha hb)
      (actualSigma a b d hd hd1 hd2 ha hb) (actualSigmaTau a b d hd hd1 hd2 ha hb)
      orders columns : SiegelZeros.W10.rootField a b) =
      (W36.concreteThetaMatrix a b d hd hd1 hd2 ha hb orders columns).det := by
  unfold deltaIntegral
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap]
  erw [RingHom.map_det]
  congr 1
  funext i j
  exact rowIntegral_eq_concreteThetaMatrix a b d hd hd1 hd2 ha hb orders columns i j

end SiegelZerosAwei.W37

end

end SiegelZeros

end OAI
