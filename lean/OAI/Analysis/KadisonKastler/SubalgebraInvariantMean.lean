import OAI.Analysis.KadisonKastler.InvariantOperatorMean
import OAI.Analysis.KadisonKastler.Algebra

namespace OAI

/-! # Restricting an invariant operator mean to a von Neumann algebra

The coefficient construction preserves every von Neumann algebra. Restricting
its domain and codomain therefore gives the exact mean for internal unitary
correction, without a normality or injectivity assumption on the target.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance subalgebraFamilyCStar (N : VonNeumannAlgebra H) :
    CStarAlgebra (G →ᵇ Algebra N) where

/-- Pointwise inclusion of bounded algebra-valued families. -/
def ambientAlgebraFamily (N : VonNeumannAlgebra H) :
    (G →ᵇ Algebra N) →⋆ₐ[ℂ] (G →ᵇ (H →L[ℂ] H)) where
  toFun F := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => (F g : H →L[ℂ] H)) ‖F‖ (fun g => F.norm_coe_le_norm g)
  map_one' := by ext g; rfl
  map_mul' _ _ := by ext g; rfl
  map_zero' := by ext g; rfl
  map_add' _ _ := by ext g; rfl
  commutes' _ := by ext g; rfl
  map_star' _ := by ext g; rfl

omit [Group G] in
@[simp]
theorem ambientAlgebraFamily_apply (N : VonNeumannAlgebra H)
    (F : G →ᵇ Algebra N) (g : G) : ambientAlgebraFamily N F g = (F g : H →L[ℂ] H) := rfl

omit [Group G] in
theorem norm_ambientAlgebraFamily_le (N : VonNeumannAlgebra H) (F : G →ᵇ Algebra N) :
    ‖ambientAlgebraFamily N F‖ ≤ ‖F‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr (fun g => F.norm_coe_le_norm g)

namespace ScalarInvariantMean

variable (m : ScalarInvariantMean G) (N : VonNeumannAlgebra H)

/-- The actual algebra-valued mean. -/
def algebraMean : (G →ᵇ Algebra N) →L[ℂ] Algebra N :=
  LinearMap.mkContinuous
    { toFun F := ⟨m.operatorMean (ambientAlgebraFamily N F),
        m.operatorMean_mem N _ (fun g => (F g).property)⟩
      map_add' F J := by
        apply Subtype.ext
        simp only [map_add, AddMemClass.coe_add]
      map_smul' c F := by
        apply Subtype.ext
        change m.operatorMean (ambientAlgebraFamily N (c • F)) =
          c • m.operatorMean (ambientAlgebraFamily N F)
        have h : ambientAlgebraFamily N (c • F) = c • ambientAlgebraFamily N F :=
          (ambientAlgebraFamily N).toAlgHom.toLinearMap.map_smul c F
        rw [h, map_smul] }
    1 (fun F => by
      change ‖m.operator (ambientAlgebraFamily N F)‖ ≤ 1 * ‖F‖
      rw [one_mul]
      exact (m.norm_operator_le _).trans (norm_ambientAlgebraFamily_le N F))

@[simp]
theorem algebraMean_coe (F : G →ᵇ Algebra N) :
    (m.algebraMean N F : H →L[ℂ] H) = m.operatorMean (ambientAlgebraFamily N F) := rfl

theorem algebraMean_norm_le (F : G →ᵇ Algebra N) : ‖m.algebraMean N F‖ ≤ ‖F‖ :=
  (m.norm_operator_le _).trans (norm_ambientAlgebraFamily_le N F)

theorem algebraMean_const (b : Algebra N) :
    m.algebraMean N (boundaryConstant b) = b := by
  apply Subtype.ext
  exact m.operatorMean_const b.val

theorem algebraMean_star (F : G →ᵇ Algebra N) :
    m.algebraMean N (star F) = star (m.algebraMean N F) := by
  apply Subtype.ext
  change m.operatorMean (ambientAlgebraFamily N (star F)) =
    star (m.operatorMean (ambientAlgebraFamily N F))
  rw [map_star]
  exact m.bimoduleMean.map_star _

theorem algebraMean_left (b : Algebra N) (F : G →ᵇ Algebra N) :
    m.algebraMean N (boundaryConstant b * F) = b * m.algebraMean N F := by
  apply Subtype.ext
  exact m.operatorMean_left b.val (ambientAlgebraFamily N F)

theorem algebraMean_right (F : G →ᵇ Algebra N) (b : Algebra N) :
    m.algebraMean N (F * boundaryConstant b) = m.algebraMean N F * b := by
  apply Subtype.ext
  exact m.operatorMean_right b.val (ambientAlgebraFamily N F)

/-- The algebra-valued mean satisfies the two module identities. -/
def algebraBimoduleMean : BimoduleMean (boundaryConstant (G := G) (B := Algebra N)) where
  toCLM := m.algebraMean N
  map_one := m.algebraMean_const N 1
  map_star := m.algebraMean_star N
  norm_le := m.algebraMean_norm_le N
  map_left := m.algebraMean_left N
  map_right := m.algebraMean_right N

/-- Translation invariance survives restriction to the algebra. -/
theorem algebraMean_translate (g : G) (F : G →ᵇ Algebra N) :
    m.algebraMean N (boundaryTranslate (1 : G →* (Algebra N ≃⋆ₐ[ℂ] Algebra N)) g F) =
      m.algebraMean N F := by
  apply Subtype.ext
  exact m.bimoduleMean_trivial_equivariant g (ambientAlgebraFamily N F)

end ScalarInvariantMean

end

end KadisonKastler

end OAI
