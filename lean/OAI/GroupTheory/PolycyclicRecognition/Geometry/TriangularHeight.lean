import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalHeight
import Mathlib.Algebra.Lie.Engel
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace OAI

/-!
# Diagonal adjoint characters and the zero-height case

Starting from an actual simultaneous upper triangular basis for the adjoint
action, the diagonal entries are linear characters and kill every bracket.
The resulting canonical height space is zero exactly when the Lie algebra is
nilpotent. This proves the algebraic zero-height branch used in the manuscript;
it does not assume nilpotence from vanishing height.
-/

namespace PolycyclicRecognition

open Module

private theorem upperTriangular_mul_diag {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

private theorem upperTriangular_pow_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (k : ℕ) (i : Fin n) :
    (A ^ k) i i = (A i i) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, upperTriangular_mul_diag _ _ (hA.pow k) hA, ih, pow_succ]

theorem upperTriangular_nilpotent_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (hnil : IsNilpotent A) (i : Fin n) : A i i = 0 := by
  obtain ⟨k, hk⟩ := hnil
  apply IsNilpotent.eq_zero
  refine ⟨k, ?_⟩
  rw [← upperTriangular_pow_diag A hA k i, hk]
  rfl

theorem upperTriangular_nilpotent_of_diag_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsUpperTriangular)
    (hz : ∀ i, A i i = 0) : IsNilpotent A := by
  have hp : A.charpoly = Polynomial.X ^ n := by
    rw [Matrix.charpoly_of_isUpperTriangular A hA]
    simp [hz]
  refine ⟨n, ?_⟩
  have h := Matrix.aeval_self_charpoly A
  simpa only [hp, map_pow, Polynomial.aeval_X] using h

/-- A simultaneous real upper triangular adjoint basis, including its actual
matrix inequalities. This is the linear-algebra meaning of real triangulability. -/
structure TriangularAdjoint (L : Type*) [LieRing L] [LieAlgebra ℝ L] (n : ℕ) where
  basis : Basis (Fin n) ℝ L
  upper : ∀ x : L, (LinearMap.toMatrix basis basis (LieAlgebra.ad ℝ L x)).IsUpperTriangular

namespace TriangularAdjoint

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
variable (T : TriangularAdjoint L n)

/-- The diagonal entries of the adjoint representation are linear forms. -/
noncomputable def character (i : Fin n) : L →ₗ[ℝ] ℝ where
  toFun x := T.basis.repr ⁅x, T.basis i⁆ i
  map_add' x y := by simp [add_lie]
  map_smul' r x := by simp [smul_lie]

@[simp] theorem character_eq_diag (i : Fin n) (x : L) :
    T.character i x = LinearMap.toMatrix T.basis T.basis (LieAlgebra.ad ℝ L x) i i := by
  simp [character, LinearMap.toMatrix_apply]

/-- The diagonal of a commutator of upper triangular matrices vanishes. -/
theorem character_lie (i : Fin n) (x y : L) : T.character i ⁅x, y⁆ = 0 := by
  have had : LieAlgebra.ad ℝ L ⁅x, y⁆ =
      LieAlgebra.ad ℝ L x * LieAlgebra.ad ℝ L y -
        LieAlgebra.ad ℝ L y * LieAlgebra.ad ℝ L x := by
    ext z
    change ⁅⁅x, y⁆, z⁆ = ⁅x, ⁅y, z⁆⁆ - ⁅y, ⁅x, z⁆⁆
    exact lie_lie x y z
  rw [character_eq_diag, had, map_sub, LinearMap.toMatrix_mul,
    LinearMap.toMatrix_mul, Matrix.sub_apply,
    upperTriangular_mul_diag _ _ (T.upper x) (T.upper y),
    upperTriangular_mul_diag _ _ (T.upper y) (T.upper x), mul_comm, sub_self]

/-- The canonical height map kills the Lie bracket, so its quotient is abelian. -/
theorem height_lie (x y : L) : heightProjection T.character ⁅x, y⁆ = 0 :=
  heightProjection_lie_eq_zero T.character T.character_lie x y

/-- The common character kernel is a Lie ideal, not just a linear subspace. -/
noncomputable def kernelIdeal : LieIdeal ℝ L where
  __ := heightKernel T.character
  lie_mem := by
    intro x y _
    exact (mem_heightKernel T.character _).mpr fun i => T.character_lie i x y

@[simp] theorem mem_kernelIdeal (x : L) :
    x ∈ T.kernelIdeal ↔ ∀ i, T.character i x = 0 := mem_heightKernel T.character x

/-- Every element of the height kernel acts nilpotently on the entire Lie algebra. -/
theorem ad_nilpotent_of_mem_kernel (x : L) (hx : x ∈ T.kernelIdeal) :
    IsNilpotent (LieAlgebra.ad ℝ L x) := by
  have hz (i : Fin n) :
      LinearMap.toMatrix T.basis T.basis (LieAlgebra.ad ℝ L x) i i = 0 := by
    rw [← T.character_eq_diag]
    exact (T.mem_kernelIdeal x).mp hx i
  obtain ⟨k, hk⟩ := upperTriangular_nilpotent_of_diag_zero _ (T.upper x) hz
  refine ⟨k, (LinearMap.toMatrixAlgEquiv T.basis).injective ?_⟩
  rw [map_pow, map_zero]
  exact hk

/-- Conversely, a nilpotent adjoint operator has zero diagonal characters. -/
theorem mem_kernelIdeal_of_ad_nilpotent (x : L)
    (hx : IsNilpotent (LieAlgebra.ad ℝ L x)) : x ∈ T.kernelIdeal := by
  apply (T.mem_kernelIdeal x).mpr
  intro i
  rw [T.character_eq_diag]
  exact upperTriangular_nilpotent_diag _ (T.upper x)
    (hx.map (LinearMap.toMatrixAlgEquiv T.basis).toRingHom) i

variable [FiniteDimensional ℝ L]

/-- Engel's theorem applied to the faithful restricted adjoint module proves
nilpotence of the common character kernel. -/
theorem kernelIdeal_nilpotent : LieRing.IsNilpotent T.kernelIdeal := by
  have : LieModule.IsNilpotent T.kernelIdeal L :=
    (LieModule.isNilpotent_iff_forall' (R := ℝ)).mpr fun x =>
      T.ad_nilpotent_of_mem_kernel x x.property
  exact (T.kernelIdeal.incl_injective).lieModuleIsNilpotent
    (f := LieHom.id) (g := T.kernelIdeal.incl.toLinearMap) (fun _ _ => rfl)

/-- The zero-height case really is nilpotent, by the triangular adjoint matrices
and Engel's theorem. -/
theorem nilpotent_of_height_zero [Subsingleton (HeightSpace T.character)] :
    LieRing.IsNilpotent L := by
  apply (LieAlgebra.isNilpotent_iff_forall (R := ℝ) (L := L)).mpr
  intro x
  have hz (i : Fin n) :
      LinearMap.toMatrix T.basis T.basis (LieAlgebra.ad ℝ L x) i i = 0 := by
    rw [← T.character_eq_diag, characters_zero_of_heightSpace_subsingleton T.character i]
    rfl
  obtain ⟨k, hk⟩ := upperTriangular_nilpotent_of_diag_zero _ (T.upper x) hz
  refine ⟨k, (LinearMap.toMatrixAlgEquiv T.basis).injective ?_⟩
  rw [map_pow, map_zero]
  exact hk

theorem height_zero_of_nilpotent [LieRing.IsNilpotent L] :
    Subsingleton (HeightSpace T.character) := by
  apply heightSpace_subsingleton_of_characters_zero
  intro i
  ext x
  rw [T.character_eq_diag]
  apply upperTriangular_nilpotent_diag _ (T.upper x)
  exact ((LieAlgebra.isNilpotent_iff_forall (R := ℝ) (L := L)).mp inferInstance x).map
    (LinearMap.toMatrixAlgEquiv T.basis).toRingHom

omit [FiniteDimensional ℝ L] in
/-- An element of a nilpotent ideal acts nilpotently on the whole algebra:
its first adjoint image lies in the ideal, where subsequent powers vanish. -/
theorem ad_nilpotent_of_mem_nilpotent_ideal
    (I : LieIdeal ℝ L) [LieRing.IsNilpotent I] (x : L) (hx : x ∈ I) :
    IsNilpotent (LieAlgebra.ad ℝ L x) := by
  let xi : I := ⟨x, hx⟩
  let f : L →ₗ[ℝ] I := (LieAlgebra.ad ℝ L x).codRestrict I.toSubmodule
    (fun y => lie_mem_left ℝ L I x y hx)
  have hp (k : ℕ) (y : L) :
      ((LieAlgebra.ad ℝ L x) ^ (k + 1)) y =
        (((LieAlgebra.ad ℝ I xi) ^ k) (f y) : I) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      rfl
  obtain ⟨k, hk⟩ := LieAlgebra.nilpotent_ad_of_nilpotent_algebra (R := ℝ) (L := I)
  refine ⟨k + 1, ?_⟩
  ext y
  rw [hp, hk xi]
  rfl

omit [FiniteDimensional ℝ L] in
/-- The canonical character kernel contains every nilpotent Lie ideal. Together
with `kernelIdeal_nilpotent`, this identifies it as the nilradical. -/
theorem nilpotent_ideal_le_kernelIdeal
    (I : LieIdeal ℝ L) [LieRing.IsNilpotent I] : I ≤ T.kernelIdeal := by
  intro x hx
  apply (T.mem_kernelIdeal x).mpr
  intro i
  rw [T.character_eq_diag]
  apply upperTriangular_nilpotent_diag _ (T.upper x)
  exact (ad_nilpotent_of_mem_nilpotent_ideal I x hx).map
    (LinearMap.toMatrixAlgEquiv T.basis).toRingHom

end TriangularAdjoint
end PolycyclicRecognition

end OAI
