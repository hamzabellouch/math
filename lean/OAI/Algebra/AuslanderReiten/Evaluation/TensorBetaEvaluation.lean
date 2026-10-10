import OAI.Algebra.AuslanderReiten.Evaluation.TensorBeta

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.A

variable {k : Type*} [Field k] (q : k)

def barZeroCoordinate : (A k q) ⊗[k] (Resolution.Simple q ⊗[k] Resolution.Simple q) →ₗ[k] A k q :=
  (TensorProduct.rid k (A k q)).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : A k q →ₗ[k] A k q) (simpleCoordinate q))

@[simp] theorem barZeroCoordinate_tmul (a : A k q) (x : Simple q) :
    barZeroCoordinate q (a ⊗ₜ[k] x) = simpleCoordinate q x • a := by
  change (TensorProduct.rid k (A k q)) (a ⊗ₜ[k] simpleCoordinate q x) = _
  exact TensorProduct.rid_tmul _ _

theorem squareEvaluation_eq_beta (H : kˣ) (hq1 : 1 + q ≠ 0)
    (s t : Resolution.Simple q) :
    barZeroCoordinate q
      (T.squareEvaluation q s t (T.twistedCasimir q H ⊗ₜ[k] T.twistedCasimir q H)) =
      (H : k)^2 • socleMap q (s ⊗ₜ[k] t) := by
  rw [T.twistedCasimir_square_evaluation q H hq1]
  simp [barZeroCoordinate, simpleCoordinate, socleMap_tmul, T.socleMap, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_smul, mul_comm]

theorem squareEvaluation_coordinate_ne_zero (H : kˣ) (hq1 : 1 + q ≠ 0) :
    barZeroCoordinate q (T.squareEvaluation q (CocycleData.simpleGenerator q)
      (CocycleData.simpleGenerator q) (T.twistedCasimir q H ⊗ₜ[k] T.twistedCasimir q H)) ≠ 0 := by
  rw [squareEvaluation_eq_beta q H hq1]
  change (H : k)^2 • socleMap q (simpleGenerator q) ≠ 0
  intro hz
  have hh := congrArg (betaDetector q) hz
  rw [map_smul, socleMap_generator, betaDetector_socle, map_zero, smul_eq_mul, mul_one] at hh
  exact pow_ne_zero 2 H.ne_zero hh

end ArExplicit.A

end

end OAI
