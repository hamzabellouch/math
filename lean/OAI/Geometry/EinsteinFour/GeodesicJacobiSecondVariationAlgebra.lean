import OAI.Geometry.EinsteinFour.GeodesicJacobiAlgebra

namespace OAI

/-! Finite metric algebra for the second variation of energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def jacobiMetricPair (G : Mat4) (v w : JacobiCoordinateVector) : ℝ :=
  v ⬝ᵥ (G *ᵥ w)

theorem jacobiMetricPair_symm {G : Mat4} (hG : G.IsSymm)
    (v w : JacobiCoordinateVector) : jacobiMetricPair G v w = jacobiMetricPair G w v :=
  hG.dotProduct_mulVec_comm

theorem jacobiMetricPair_add_left (G : Mat4) (u v w : JacobiCoordinateVector) :
    jacobiMetricPair G (u + v) w = jacobiMetricPair G u w + jacobiMetricPair G v w := by
  exact add_dotProduct _ _ _

theorem jacobiMetricPair_add_right (G : Mat4) (u v w : JacobiCoordinateVector) :
    jacobiMetricPair G u (v + w) = jacobiMetricPair G u v + jacobiMetricPair G u w := by
  simp only [jacobiMetricPair, Matrix.mulVec_add, dotProduct_add]

theorem jacobiMetricPair_smul_right (G : Mat4) (u v : JacobiCoordinateVector) (r : ℝ) :
    jacobiMetricPair G u (r • v) = r * jacobiMetricPair G u v := by
  simp only [jacobiMetricPair, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem jacobiMetricPair_neg_left (G : Mat4) (u v : JacobiCoordinateVector) :
    jacobiMetricPair G (-u) v = -jacobiMetricPair G u v := by
  exact neg_dotProduct _ _

theorem jacobiMetricPair_matrix_add (G H : Mat4) (v w : JacobiCoordinateVector) :
    jacobiMetricPair (G + H) v w = jacobiMetricPair G v w + jacobiMetricPair H v w := by
  simp only [jacobiMetricPair, Matrix.add_mulVec, dotProduct_add]

theorem jacobiMetricPair_left_product (G A : Mat4) (v w : JacobiCoordinateVector) :
    jacobiMetricPair (Aᵀ * G) v w = jacobiMetricPair G (A *ᵥ v) w := by
  simp only [jacobiMetricPair, ← Matrix.mulVec_mulVec,
    dotProduct_transpose_mulVec A v (G *ᵥ w), dotProduct_comm]

theorem jacobiMetricPair_right_product (G A : Mat4) (v w : JacobiCoordinateVector) :
    jacobiMetricPair (G * A) v w = jacobiMetricPair G v (A *ᵥ w) := by
  simp only [jacobiMetricPair, Matrix.mulVec_mulVec]

def jacobiMetricRate (G A : Mat4) : Mat4 := Aᵀ * G + G * A

def jacobiMetricSecondRate (G B C : Mat4) : Mat4 :=
  Cᵀ * G + Bᵀ * jacobiMetricRate G B + jacobiMetricRate G B * B + G * C

theorem jacobiMetricRate_pair (G A : Mat4) (v w : JacobiCoordinateVector) :
    jacobiMetricPair (jacobiMetricRate G A) v w =
      jacobiMetricPair G (A *ᵥ v) w + jacobiMetricPair G v (A *ᵥ w) := by
  rw [jacobiMetricRate, jacobiMetricPair_matrix_add,
    jacobiMetricPair_left_product, jacobiMetricPair_right_product]

theorem jacobiMetricRate_symm {G : Mat4} (hG : G.IsSymm) (A : Mat4) :
    (jacobiMetricRate G A).IsSymm := by
  change (Aᵀ * G + G * A)ᵀ = Aᵀ * G + G * A
  simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hG.eq]
  exact add_comm _ _

theorem jacobiMetricSecondRate_pair_self {G : Mat4} (hG : G.IsSymm)
    (B C : Mat4) (v : JacobiCoordinateVector) :
    (1 / 2 : ℝ) * jacobiMetricPair (jacobiMetricSecondRate G B C) v v =
      jacobiMetricPair G v (C *ᵥ v) + jacobiMetricPair G (B *ᵥ v) (B *ᵥ v) +
        jacobiMetricPair G v (B *ᵥ (B *ᵥ v)) := by
  have hsum : jacobiMetricSecondRate G B C =
      jacobiMetricRate G C + jacobiMetricRate (jacobiMetricRate G B) B := by
    unfold jacobiMetricSecondRate jacobiMetricRate
    abel
  rw [hsum, jacobiMetricPair_matrix_add, jacobiMetricRate_pair,
    jacobiMetricRate_pair, jacobiMetricPair_symm hG (C *ᵥ v) v,
    jacobiMetricPair_symm (jacobiMetricRate_symm hG B) (B *ᵥ v) v,
    jacobiMetricRate_pair]
  ring

def coordinateEnergySecondDensity (G H K : Mat4) (v w : JacobiCoordinateVector) : ℝ :=
  jacobiMetricPair G w w + 2 * jacobiMetricPair H w v +
    (1 / 2 : ℝ) * jacobiMetricPair K v v

theorem coordinateEnergySecondDensity_expansion {G : Mat4} (hG : G.IsSymm)
    (B C : Mat4) (v w : JacobiCoordinateVector) :
    coordinateEnergySecondDensity G (jacobiMetricRate G B) (jacobiMetricSecondRate G B C) v w =
      jacobiMetricPair G w w + 2 * jacobiMetricPair G w (B *ᵥ v) +
        2 * jacobiMetricPair G v (B *ᵥ w) + jacobiMetricPair G v (C *ᵥ v) +
        jacobiMetricPair G (B *ᵥ v) (B *ᵥ v) +
        jacobiMetricPair G v (B *ᵥ (B *ᵥ v)) := by
  rw [coordinateEnergySecondDensity, jacobiMetricSecondRate_pair_self hG,
    jacobiMetricRate_pair, jacobiMetricPair_symm hG (B *ᵥ w) v]
  ring

theorem jacobiMetricPair_skew {G K : Mat4}
    (hK : Kᵀ * G + G * K = 0) (v y : JacobiCoordinateVector) :
    jacobiMetricPair G (K *ᵥ v) y = -jacobiMetricPair G v (K *ᵥ y) := by
  have h := congrArg (fun A : Mat4 => jacobiMetricPair A v y) hK
  rw [jacobiMetricPair_matrix_add, jacobiMetricPair_left_product,
    jacobiMetricPair_right_product] at h
  have hz : jacobiMetricPair (0 : Mat4) v y = 0 := by
    simp [jacobiMetricPair]
  rw [hz] at h
  linarith

/-- The vector terms left after adding the boundary derivative to the
curvature term collapse by torsion freedom and its derivative. -/
theorem jacobiSecondVariation_vector_identity (Γ : Fin 4 → Mat4)
    (D : Fin 4 → Fin 4 → Mat4)
    (hΓ : ∀ a i j, Γ i a j = Γ j a i)
    (hD : ∀ r a i j, D r i a j = D r j a i)
    (v y : JacobiCoordinateVector) :
    jacobiCurvature Γ D y v *ᵥ y +
        jacobiConnection Γ v *ᵥ (jacobiConnection Γ y *ᵥ y) +
        jacobiConnectionDerivative D v y *ᵥ y =
      jacobiConnectionDerivative D y y *ᵥ v +
        jacobiConnection Γ y *ᵥ (jacobiConnection Γ y *ᵥ v) := by
  rw [jacobiCurvature_eq, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    jacobiConnection_mulVec_comm Γ hΓ v y,
    jacobiConnectionDerivative_mulVec_comm D hD y v y]
  module

def coordinateIndexDensity (G : Mat4) (Γ : Fin 4 → Mat4)
    (D : Fin 4 → Fin 4 → Mat4) (v y w : JacobiCoordinateVector) : ℝ :=
  jacobiMetricPair G (w + jacobiConnection Γ v *ᵥ y)
      (w + jacobiConnection Γ v *ᵥ y) -
    jacobiMetricPair G (jacobiCurvature Γ D y v *ᵥ v) y

def coordinateEnergyBoundaryRate (G : Mat4) (Γ : Fin 4 → Mat4)
    (D : Fin 4 → Fin 4 → Mat4) (v y w : JacobiCoordinateVector) : ℝ :=
  jacobiMetricPair G v
    (jacobiConnection Γ v *ᵥ (jacobiConnection Γ y *ᵥ y) +
      jacobiConnectionDerivative D v y *ᵥ y +
      (2 : ℝ) • (jacobiConnection Γ y *ᵥ w))

/-- The full pointwise second-variation identity. -/
theorem coordinateEnergySecondDensity_eq_index_add_boundary
    (G : Mat4) (Γ : Fin 4 → Mat4) (D : Fin 4 → Fin 4 → Mat4)
    (hG : G.IsSymm) (hΓ : ∀ a i j, Γ i a j = Γ j a i)
    (hD : ∀ r a i j, D r i a j = D r j a i)
    (v y w : JacobiCoordinateVector)
    (hK : (jacobiCurvature Γ D y v)ᵀ * G + G * jacobiCurvature Γ D y v = 0) :
    coordinateEnergySecondDensity G (jacobiMetricRate G (jacobiConnection Γ y))
        (jacobiMetricSecondRate G (jacobiConnection Γ y) (jacobiConnectionDerivative D y y)) v w =
      coordinateIndexDensity G Γ D v y w + coordinateEnergyBoundaryRate G Γ D v y w := by
  have hAy := jacobiConnection_mulVec_comm Γ hΓ v y
  have hvec := jacobiSecondVariation_vector_identity Γ D hΓ hD v y
  have hpair := congrArg (fun u => jacobiMetricPair G v u) hvec
  simp only [jacobiMetricPair_add_right] at hpair
  rw [coordinateEnergySecondDensity_expansion hG]
  unfold coordinateIndexDensity coordinateEnergyBoundaryRate
  rw [jacobiMetricPair_skew hK, hAy]
  simp only [jacobiMetricPair_add_left, jacobiMetricPair_add_right,
    jacobiMetricPair_smul_right]
  rw [jacobiMetricPair_symm hG (jacobiConnection Γ y *ᵥ v) w]
  linarith

end
end PositiveEinsteinFour.Geometry

end OAI
