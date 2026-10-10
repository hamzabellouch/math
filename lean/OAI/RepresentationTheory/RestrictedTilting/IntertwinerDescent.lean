import Mathlib

namespace OAI

 

noncomputable section
open scoped BigOperators

namespace FiberFunctorProof

 

lemma invertible_linear_combination
    {k K : Type*} [Field k] [Infinite k] [Field K] [Algebra k K]
    {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (M : ι → Matrix n n k) (v : ι → K)
    (hv : (∑ a : ι, v a • (M a).map (algebraMap k K)).det ≠ 0) :
    ∃ c : ι → k, (∑ a : ι, c a • M a).det ≠ 0 := by
  classical
  let P : Matrix n n (MvPolynomial ι k) :=
    fun i j => ∑ a : ι, MvPolynomial.C (M a i j) * MvPolynomial.X a
  have hP : P.det ≠ 0 := by
    intro hzero
    apply hv
    have heval : P.map (MvPolynomial.eval₂Hom (algebraMap k K) v) =
        ∑ a : ι, v a • (M a).map (algebraMap k K) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply]
      dsimp [P]
      simp [mul_comm]
    rw [← heval, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hzero, map_zero]
  have hex : ∃ c : ι → k, MvPolynomial.eval c P.det ≠ 0 := by
    by_contra! h
    apply hP
    apply MvPolynomial.funext
    intro c
    simpa only [map_zero] using h c
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, ?_⟩
  have heval : P.map (MvPolynomial.eval c) = ∑ a : ι, c a • M a := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply]
    dsimp [P]
    simp [mul_comm]
  rwa [← heval, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

 

theorem intertwiner_descent
    {k K : Type*} [Field k] [Infinite k] [Field K] [Algebra k K]
    {n : Type*} [Fintype n] [DecidableEq n] {G : Type*}
    (A B : G → Matrix n n k)
    (C : Matrix n n K) (hC : C.det ≠ 0)
    (h : ∀ g, (A g).map (algebraMap k K) * C = C * (B g).map (algebraMap k K)) :
    ∃ D : Matrix n n k, D.det ≠ 0 ∧ ∀ g, A g * D = D * B g := by
  classical
  let W : Submodule k K := Submodule.span k (Set.range (fun ij : n × n => C ij.1 ij.2))
  have : FiniteDimensional k W := FiniteDimensional.span_of_finite k (Set.finite_range _)
  let b := Module.finBasis k W
  let V : Matrix n n W := fun i j => ⟨C i j, Submodule.subset_span ⟨(i, j), rfl⟩⟩
  let M : Fin (Module.finrank k W) → Matrix n n k := fun a i j => b.repr (V i j) a
  have hrepr : C = ∑ a, (b a : K) • (M a).map (algebraMap k K) := by
    ext i j
    have heq := congrArg (fun x : W => (x : K)) (b.sum_repr (V i j))
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply]
    change (V i j : K) = ∑ a, (b a : K) * algebraMap k K (b.repr (V i j) a)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def] at heq
    exact heq.symm.trans (Finset.sum_congr rfl fun a _ => mul_comm _ _)
  have hM : ∀ a g, A g * M a = M a * B g := by
    intro a g
    ext i j
    have hW : ∑ l : n, A g i l • V l j = ∑ l : n, B g l j • V i l := by
      apply Subtype.val_injective
      have heq := congrArg (fun X : Matrix n n K => X i j) (h g)
      simp only [Matrix.mul_apply, Matrix.map_apply] at heq
      simp only [Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def]
      exact heq.trans (Finset.sum_congr rfl fun l _ => mul_comm _ _)
    have heq := congrArg (b.coord a) hW
    simp only [Matrix.mul_apply]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply] at heq
    exact heq.trans (Finset.sum_congr rfl fun l _ => mul_comm _ _)
  have hcomb : (∑ a, (b a : K) • (M a).map (algebraMap k K)).det ≠ 0 := by
    rwa [← hrepr]
  obtain ⟨c, hc⟩ := invertible_linear_combination M (fun a => (b a : K)) hcomb
  refine ⟨∑ a, c a • M a, hc, ?_⟩
  intro g
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hM]

end FiberFunctorProof

end

end OAI
