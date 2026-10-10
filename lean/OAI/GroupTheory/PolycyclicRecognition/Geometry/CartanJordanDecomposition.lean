import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWeightDerivation
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

namespace OAI

/-! # Identifying the Cartan weight operator as the semisimple part

The polynomial Jordan decomposition shows that the weight operator preserves
every subspace preserved by the original adjoint operator. This will keep the
original triangular flag when the weight operator is subtracted.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

theorem cartanWeightOperator_jordan (h : H) :
    cartanWeightOperator T H h ∈ Algebra.adjoin ℝ {ad ℝ L (h : L)} ∧
      IsNilpotent (ad ℝ L (h : L) - cartanWeightOperator T H h) := by
  obtain ⟨N, hN, S, hS, hnil, hss, hsum⟩ :=
    (ad ℝ L (h : L)).exists_isNilpotent_isSemisimple
  have hc : Commute (ad ℝ L (h : L)) S :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hS (Commute.refl _)
  have hd : IsNilpotent (ad ℝ L (h : L) - S) := by
    simpa only [hsum, add_sub_cancel_right] using hnil
  have heq : S = cartanWeightOperator T H h := by
    ext x
    apply cartan_root_induction T H (x := x)
    · intro χ v hv
      rw [cartanWeightOperator_apply_root T H h χ hv]
      have hv' : v ∈ (ad ℝ L (h : L)).maxGenEigenspace (χ h) :=
        genWeightSpace_le_genWeightSpaceOf L h χ hv
      exact End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
        hv' hc hss.isFinitelySemisimple hd
    · simp
    · intro u v hu hv
      simp only [map_add, hu, hv]
  exact ⟨heq ▸ hS, heq ▸ hd⟩

theorem cartanWeightOperator_upper (h : H) :
    (LinearMap.toMatrix T.basis T.basis (cartanWeightOperator T H h)).IsUpperTriangular := by
  let F := LinearMap.toMatrixAlgEquiv T.basis
  let A := Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin n → Fin n)
  have hle : Algebra.adjoin ℝ {ad ℝ L (h : L)} ≤ A.comap F.toAlgHom := by
    apply Algebra.adjoin_le
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact T.upper h
  exact hle (cartanWeightOperator_jordan T H h).1

/-- Removing the semisimple height action leaves a strictly triangular
operator in the original adjoint flag. -/
theorem heightReducedAdjoint_nilpotent (x : L) :
    IsNilpotent (ad ℝ L x - (heightSemisimpleAction T H x).toLinearMap) := by
  let h := cartanHeightSection T H (heightProjection T.character x)
  let u : L := x - (h : L)
  let N := ad ℝ L (h : L) - cartanWeightOperator T H h
  have hN : IsNilpotent N := (cartanWeightOperator_jordan T H h).2
  have hNu : (LinearMap.toMatrix T.basis T.basis N).IsUpperTriangular := by
    rw [show N = ad ℝ L (h : L) - cartanWeightOperator T H h from rfl, map_sub]
    exact (T.upper h).sub (cartanWeightOperator_upper T H h)
  have hNd (i : Fin n) : LinearMap.toMatrix T.basis T.basis N i i = 0 :=
    upperTriangular_nilpotent_diag _ hNu
      (hN.map (LinearMap.toMatrixAlgEquiv T.basis).toRingHom) i
  have huk : u ∈ T.kernelIdeal := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change heightProjection T.character (x - (h : L)) = 0
    rw [map_sub, cartanHeightSection_height, sub_self]
  have hud (i : Fin n) : LinearMap.toMatrix T.basis T.basis (ad ℝ L u) i i = 0 := by
    rw [← T.character_eq_diag]
    exact (T.mem_kernelIdeal u).mp huk i
  have heq : ad ℝ L x - (heightSemisimpleAction T H x).toLinearMap = ad ℝ L u + N := by
    change ad ℝ L x - cartanWeightOperator T H h = ad ℝ L (x - (h : L)) + N
    rw [map_sub]
    dsimp only [N]
    abel
  rw [heq]
  obtain ⟨k, hk⟩ := upperTriangular_nilpotent_of_diag_zero
    (LinearMap.toMatrix T.basis T.basis (ad ℝ L u + N))
    (by rw [map_add]; exact (T.upper u).add hNu)
    (by intro i; simp only [map_add, Matrix.add_apply, hud, hNd, add_zero])
  refine ⟨k, (LinearMap.toMatrixAlgEquiv T.basis).injective ?_⟩
  rw [map_pow, map_zero]
  change (LinearMap.toMatrix T.basis T.basis (ad ℝ L u + N)) ^ k = 0
  exact hk

end PolycyclicRecognition

end

end OAI
