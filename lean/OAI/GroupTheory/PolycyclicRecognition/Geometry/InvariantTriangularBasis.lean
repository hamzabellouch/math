import OAI.GroupTheory.PolycyclicRecognition.Algebra.BasisQuotientLifts
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Isomorphisms

namespace OAI

/-!
# Restricting an actual triangular action

An invariant subspace of a simultaneous real triangular action again
has a simultaneous triangular basis. The proof chooses the last
nonzero coordinate functional and inducts on its invariant kernel.
No spectral splitting or solvability hypothesis is needed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Matrix

/-- The last active coordinate of a triangular representation is a
common eigenfunctional on every nonzero invariant subspace. -/
theorem exists_triangular_eigenfunctional
    {ι W : Type*} [AddCommGroup W] [Module ℝ W] [Nontrivial W]
    {n : ℕ} (e : W →ₗ[ℝ] (Fin n → ℝ)) (he : Function.Injective e)
    (T : ι → W →ₗ[ℝ] W) (A : ι → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ x, (A x).IsUpperTriangular)
    (hinter : ∀ x v, e (T x v) = A x *ᵥ e v) :
    ∃ (p : W →ₗ[ℝ] ℝ), p ≠ 0 ∧
      ∀ x, ∃ c : ℝ, ∀ v, p (T x v) = c * p v := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i => ∃ v : W, e v i ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    have hev : e v ≠ 0 := fun h => hv (he (h.trans (map_zero e).symm))
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hev
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, v, hi⟩⟩
  let i := s.max' hs
  have hi : i ∈ s := Finset.max'_mem s hs
  have hzero : ∀ j : Fin n, i < j → ∀ v : W, e v j = 0 := by
    intro j hij v
    by_contra hj
    have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, v, hj⟩
    exact (not_le_of_gt hij) (Finset.le_max' s j hjs)
  let p : W →ₗ[ℝ] ℝ := (LinearMap.proj i).comp e
  refine ⟨p, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hi).2
    intro hp
    exact hv (congrArg (fun f : W →ₗ[ℝ] ℝ => f v) hp)
  · intro x
    refine ⟨A x i i, fun v => ?_⟩
    change e (T x v) i = A x i i * e v i
    rw [hinter, Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_single i
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with h | h
      · exact mul_eq_zero_of_left (hA x (i := i) (j := j) h) _
      · rw [hzero j h v, mul_zero]
    · simp

/-- Every action embedded into actual upper triangular matrices admits
an upper triangular basis on its own finite-dimensional space. -/
theorem exists_upperTriangular_basis_of_embedding
    {ι W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {n : ℕ} (e : W →ₗ[ℝ] (Fin n → ℝ)) (he : Function.Injective e)
    (T : ι → W →ₗ[ℝ] W) (A : ι → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ x, (A x).IsUpperTriangular)
    (hinter : ∀ x v, e (T x v) = A x *ᵥ e v) :
    ∃ (m : ℕ) (b : Basis (Fin m) ℝ W),
      ∀ x, (LinearMap.toMatrix b b (T x)).IsUpperTriangular := by
  classical
  by_cases hzero : finrank ℝ W = 0
  · refine ⟨finrank ℝ W, Module.finBasis ℝ W, ?_⟩
    intro x i j hij
    have := i.isLt
    omega
  let : Nontrivial W := finrank_pos_iff.mp (Nat.pos_of_ne_zero hzero)
  obtain ⟨p, hp, hscalar⟩ := exists_triangular_eigenfunctional e he T A hA hinter
  let N := p.ker
  have hN : ∀ x, ∀ v ∈ N, T x v ∈ N := by
    intro x v hv
    obtain ⟨c, hc⟩ := hscalar x
    change p (T x v) = 0
    rw [hc]
    exact mul_eq_zero_of_right c hv
  let TN (x : ι) : N →ₗ[ℝ] N := (T x).restrict (hN x)
  let eN : N →ₗ[ℝ] (Fin n → ℝ) := e.comp N.subtype
  have heN : Function.Injective eN := he.comp Subtype.val_injective
  have hinterN : ∀ x v, eN (TN x v) = A x *ᵥ eN v := by
    intro x v
    exact hinter x v
  have hNlt : finrank ℝ N < finrank ℝ W := by
    apply Submodule.finrank_lt
    exact fun h => hp (LinearMap.ker_eq_top.mp h)
  obtain ⟨m, bN, hbN⟩ :=
    exists_upperTriangular_basis_of_embedding eN heN TN A hA hinterN
  have hrange : p.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    obtain ⟨v, hv⟩ : ∃ v, p v ≠ 0 := by
      by_contra! h
      exact hp (LinearMap.ext h)
    intro y
    refine ⟨(y / p v) • v, ?_⟩
    simp only [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ y hv
  have hdimQ : finrank ℝ (W ⧸ N) = 1 := by
    have heq := LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange p)
    change finrank ℝ (W ⧸ p.ker) = 1
    rw [heq, hrange, finrank_top, finrank_self]
  let bQ : Basis (Fin 1) ℝ (W ⧸ N) :=
    (Module.finBasis ℝ (W ⧸ N)).reindex (finCongr hdimQ)
  choose lift hlift using fun i : Fin 1 => N.mkQ_surjective (bQ i)
  let b := basisWithQuotientLifts N bN bQ lift hlift
  let er : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  refine ⟨m + 1, b.reindex er, ?_⟩
  intro x i j hij
  obtain ⟨i, rfl⟩ := er.surjective i
  obtain ⟨j, rfl⟩ := er.surjective j
  simp only [LinearMap.toMatrix_apply, Basis.repr_reindex_apply, Basis.reindex_apply,
    Equiv.symm_apply_apply]
  dsimp only [b]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [basisWithQuotientLifts_inl]
      change (basisWithQuotientLifts N bN bQ lift hlift).repr
        ((TN x (bN j) : N) : W) (Sum.inl i) = 0
      rw [basisWithQuotientLifts_repr_inl]
      simpa only [LinearMap.toMatrix_apply] using
        hbN x (i := i) (j := j) (by
          change (j : ℕ) < (i : ℕ) at hij ⊢
          exact hij)
    | inr j =>
      have hj : (j : ℕ) = 0 := by omega
      change m + (j : ℕ) < (i : ℕ) at hij
      have := i.isLt
      omega
  | inr i =>
    cases j with
    | inl j =>
      rw [basisWithQuotientLifts_inl, basisWithQuotientLifts_repr_inr]
      have hz : N.mkQ (T x (bN j)) = 0 :=
        (Submodule.Quotient.mk_eq_zero N).mpr (hN x (bN j) (bN j).property)
      rw [hz, map_zero, Finsupp.zero_apply]
    | inr j =>
      have heq : i = j := Subsingleton.elim i j
      exact (hij.ne (congrArg (fun a => er (Sum.inr a)) heq).symm).elim
termination_by finrank ℝ W

end PolycyclicRecognition

end

end OAI
