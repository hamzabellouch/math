import OAI.GroupTheory.PolycyclicRecognition.Geometry.SplitLieQuotient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BasisQuotientLifts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularHeight
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity

namespace OAI

/-!
# The simultaneous-basis form of Lie's theorem

Mathlib's Lie theorem supplies a common eigenvector for a solvable split
action. We iterate it on invariant quotients and lift each quotient basis,
obtaining the single upper triangular basis required by `TriangularAdjoint`.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set

/-- A finite-dimensional split action of a solvable split Lie algebra has
a simultaneous upper triangular basis. -/
theorem exists_upperTriangular_lieModule_basis {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (L V : Type*)
    [LieRing L] [LieAlgebra 𝕜 L] [LieAlgebra.IsSolvable L]
    [AddCommGroup V] [Module 𝕜 V] [LieRingModule L V] [LieModule 𝕜 L V]
    [FiniteDimensional 𝕜 V] [LieModule.IsTriangularizable 𝕜 L V] :
    ∃ (n : ℕ) (b : Basis (Fin n) 𝕜 V),
      ∀ x : L, (LinearMap.toMatrix b b (LieModule.toEnd 𝕜 L V x)).IsUpperTriangular := by
  classical
  by_cases hzero : finrank 𝕜 V = 0
  · refine ⟨finrank 𝕜 V, Module.finBasis 𝕜 V, ?_⟩
    intro x i j hij
    have := i.isLt
    omega
  have hpos : 0 < finrank 𝕜 V := Nat.pos_of_ne_zero hzero
  let : Nontrivial V := finrank_pos_iff.mp hpos
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable 𝕜 L V
  let := hχ
  obtain ⟨v, hv⟩ := exists_ne (0 : LieModule.weightSpace V χ)
  have hv0 : (v : V) ≠ 0 := by
    intro h
    exact hv (Subtype.ext h)
  have hvχ : ∀ x : L, ⁅x, (v : V)⁆ = χ x • (v : V) :=
    (LieModule.mem_weightSpace χ (v : V)).mp v.property
  let N : LieSubmodule 𝕜 L V :=
    { (𝕜 ∙ (v : V)) with
      lie_mem := by
        intro x w hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [lie_smul, hvχ]
        exact Submodule.smul_mem _ a
          (Submodule.smul_mem _ (χ x) (Submodule.mem_span_singleton_self (v : V))) }
  have hdimN : finrank 𝕜 N.toSubmodule = 1 := finrank_span_singleton hv0
  have hlt : finrank 𝕜 (V ⧸ N) < finrank 𝕜 V := by
    change finrank 𝕜 (V ⧸ N.toSubmodule) < finrank 𝕜 V
    have hd := N.toSubmodule.finrank_quotient_add_finrank
    rw [hdimN] at hd
    omega
  let : LieModule.IsTriangularizable 𝕜 L (V ⧸ N) := quotient_isTriangularizable (𝕜 := 𝕜) N
  obtain ⟨n, bQ, hQ⟩ := exists_upperTriangular_lieModule_basis (𝕜 := 𝕜) L (V ⧸ N)
  let bN : Basis (Fin 1) 𝕜 N.toSubmodule := FiniteDimensional.basisSingleton (Fin 1) hdimN
    ⟨v, Submodule.mem_span_singleton_self (v : V)⟩ (by
      intro h
      apply hv0
      exact congrArg Subtype.val h)
  choose lift hlift using fun i : Fin n => N.toSubmodule.mkQ_surjective (bQ i)
  let b := basisWithQuotientLifts N.toSubmodule bN bQ lift hlift
  let e : Fin 1 ⊕ Fin n ≃ Fin (1 + n) := finSumFinEquiv
  refine ⟨1 + n, b.reindex e, ?_⟩
  intro x i j hij
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  simp only [LinearMap.toMatrix_apply, LieModule.toEnd_apply_apply]
  simp only [Basis.repr_reindex_apply, Basis.reindex_apply, Equiv.symm_apply_apply]
  dsimp only [b]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hi : (i : ℕ) = 0 := by omega
      have hj : (j : ℕ) = 0 := by omega
      have heq : i = j := Fin.ext (hi.trans hj.symm)
      exact (hij.ne (congrArg (fun a => e (Sum.inl a)) heq).symm).elim
    | inr j =>
      have hi : (i : ℕ) = 0 := by omega
      change 1 + (j : ℕ) < (i : ℕ) at hij
      omega
  | inr i =>
    cases j with
    | inl j =>
      rw [basisWithQuotientLifts_inl, basisWithQuotientLifts_repr_inr]
      have hz : N.toSubmodule.mkQ ⁅x, (bN j : V)⁆ = 0 :=
        (Submodule.Quotient.mk_eq_zero N.toSubmodule).mpr (N.lie_mem (bN j).property)
      rw [hz, map_zero, Finsupp.zero_apply]
    | inr j =>
      rw [basisWithQuotientLifts_inr, basisWithQuotientLifts_repr_inr]
      have hq : N.toSubmodule.mkQ ⁅x, lift j⁆ =
          (LieModule.toEnd 𝕜 L (V ⧸ N) x) (bQ j) := by
        change (LieModule.toEnd 𝕜 L (V ⧸ N) x) (N.toSubmodule.mkQ (lift j)) = _
        rw [hlift]
      rw [hq]
      change 1 + (j : ℕ) < 1 + (i : ℕ) at hij
      simpa only [LinearMap.toMatrix_apply, LieModule.toEnd_apply_apply] using
        hQ x (i := i) (j := j) (by change (j : ℕ) < (i : ℕ); omega)
termination_by finrank 𝕜 V

/-- Applying the proved simultaneous-basis theorem to the adjoint module
produces exactly the basis structure used by the height construction. -/
theorem nonempty_triangularAdjoint_of_split (L : Type*)
    [LieRing L] [LieAlgebra ℝ L] [LieAlgebra.IsSolvable L]
    [FiniteDimensional ℝ L] [LieModule.IsTriangularizable ℝ L L] :
    ∃ n : ℕ, Nonempty (TriangularAdjoint L n) := by
  obtain ⟨n, b, hb⟩ := exists_upperTriangular_lieModule_basis (𝕜 := ℝ) L L
  exact ⟨n, ⟨⟨b, hb⟩⟩⟩

end PolycyclicRecognition

end

end OAI
