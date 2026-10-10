import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexNilradical
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealTorusContinuity
import Mathlib.Algebra.Lie.Weights.Chain

namespace OAI

/-! # Compact rotations act trivially on the adjoint-weight quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

namespace ComplexTriangularAdjoint
variable (T : ComplexTriangularAdjoint L n)

/-- The same adjoint diagonal on the entire complexification. -/
def complexWeightMap : (ℂ ⊗[ℝ] L) →ₗ[ℂ] (Fin n → ℂ) where
  toFun x i := LinearMap.toMatrix T.basis T.basis (ad ℂ (ℂ ⊗[ℝ] L) x) i i
  map_add' x y := by
    ext i
    simp only [map_add, Matrix.add_apply, Pi.add_apply]
  map_smul' r x := by
    ext i
    simp only [map_smul, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply]

@[simp] theorem complexWeightMap_one_tmul (x : L) :
    T.complexWeightMap ((1 : ℂ) ⊗ₜ[ℝ] x) = T.weightMap x := rfl

theorem complexWeightMap_eq_zero_iff (x : ℂ ⊗[ℝ] L) :
    T.complexWeightMap x = 0 ↔ IsNilpotent (ad ℂ (ℂ ⊗[ℝ] L) x) := by
  let A := LinearMap.toMatrix T.basis T.basis (ad ℂ (ℂ ⊗[ℝ] L) x)
  constructor
  · intro hx
    have hz (i : Fin n) : A i i = 0 := congrFun hx i
    have hp : A.charpoly = Polynomial.X ^ n := by
      rw [Matrix.charpoly_of_isUpperTriangular A (T.upper x)]
      simp [hz]
    have hA : A ^ n = 0 := by
      simpa only [hp, map_pow, Polynomial.aeval_X] using Matrix.aeval_self_charpoly A
    refine ⟨n, (LinearMap.toMatrixAlgEquiv T.basis).injective ?_⟩
    rw [map_pow, map_zero]
    exact hA
  · rintro ⟨k, hk⟩
    have hA : A ^ k = 0 := by
      change ((LinearMap.toMatrixAlgEquiv T.basis) (ad ℂ (ℂ ⊗[ℝ] L) x)) ^ k = 0
      rw [← map_pow, hk, map_zero]
    ext i
    change A i i = 0
    apply eq_zero_of_pow_eq_zero (n := k)
    rw [← diagonal_pow A (T.upper x) k i, hA]
    rfl

variable [FiniteDimensional ℝ L] (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- The nonzero Cartan root spaces lie in the common complex weight kernel. -/
theorem complexWeightMap_root_zero
    {χ : complexifiedSubalgebra L H → ℂ} (hχ : χ ≠ 0)
    {x : ℂ ⊗[ℝ] L} (hx : x ∈ rootSpace (complexifiedSubalgebra L H) χ) :
    T.complexWeightMap x = 0 :=
  (T.complexWeightMap_eq_zero_iff x).mpr
    (LieAlgebra.isNilpotent_ad_of_mem_rootSpace (complexifiedSubalgebra L H) hχ hx)

/-- All the complex weight coordinates have a common representative in the
complexified Cartan subalgebra. -/
theorem exists_complex_cartan_representative (x : ℂ ⊗[ℝ] L) :
    ∃ h : complexifiedSubalgebra L H, T.complexWeightMap h = T.complexWeightMap x := by
  apply ComplexCartan.root_induction (complexifiedSubalgebra L H) (x := x)
  · intro χ v hv
    by_cases hχ : (χ : complexifiedSubalgebra L H → ℂ) = 0
    · have hm : v ∈ complexifiedSubalgebra L H := by
        have hv' : v ∈ rootSpace (complexifiedSubalgebra L H) 0 := by
          simpa only [hχ] using hv
        rwa [rootSpace_zero_eq] at hv'
      exact ⟨⟨v, hm⟩, rfl⟩
    · refine ⟨0, ?_⟩
      change T.complexWeightMap 0 = T.complexWeightMap v
      rw [map_zero, T.complexWeightMap_root_zero H hχ hv]
  · exact ⟨0, by simp⟩
  · rintro v w ⟨h, hh⟩ ⟨k, hk⟩
    refine ⟨h + k, ?_⟩
    change T.complexWeightMap ((h : ℂ ⊗[ℝ] L) + k) = _
    rw [map_add, hh, hk, map_add]

/-- Every element of the compact rotation group fixes the whole complex
adjoint-weight quotient, not merely its kernel. -/
theorem complexWeightMap_torusOperator
    (z : complexCartanTorus L H) (x : ℂ ⊗[ℝ] L) :
    T.complexWeightMap (ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val x) =
      T.complexWeightMap x := by
  apply ComplexCartan.root_induction (complexifiedSubalgebra L H) (x := x)
  · intro χ v hv
    by_cases hχ : (χ : complexifiedSubalgebra L H → ℂ) = 0
    · have hm : v ∈ complexifiedSubalgebra L H := by
        have hv' : v ∈ rootSpace (complexifiedSubalgebra L H) 0 := by
          simpa only [hχ] using hv
        rwa [rootSpace_zero_eq] at hv'
      rw [z.property.2 ⟨v, hm⟩]
    · change T.complexWeightMap
        (ComplexCartan.weightOperator (complexifiedSubalgebra L H) _ v) = _
      rw [ComplexCartan.weightOperator_apply _ _ χ hv, map_smul,
        T.complexWeightMap_root_zero H hχ hv, smul_zero]
  · simp
  · intro v w hv hw
    simp only [map_add, hv, hw]

/-- The real compact rotation action fixes the actual real weight quotient. -/
theorem weightMap_realTorusOperator (z : realRotationTorus L H) (x : L) :
    T.weightMap (realTorusOperator L H z x) = T.weightMap x := by
  rw [← T.complexWeightMap_one_tmul, realTorusOperator_complexify,
    T.complexWeightMap_torusOperator H, T.complexWeightMap_one_tmul]

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
