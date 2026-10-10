import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.LaurentIntersection

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.LaurentLattices
noncomputable section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K N Q : Type*} [Field K] [AddCommGroup N] [AddCommGroup Q]
  [Module K N] [Module K Q] [Module K[X] N] [IsScalarTower K K[X] N]
  [Module K[T;T⁻¹] Q] [IsScalarTower K K[T;T⁻¹] Q]

omit [IsScalarTower K K[T;T⁻¹] Q] in
lemma range_le_lattice {ι : Type*} [Fintype ι] (s : ι → N)
    (hs : Submodule.span K[X] (Set.range s) = ⊤) (g : N →ₗ[K] Q) (d : ℤ)
    (hpow : ∀ (n : ℕ) (x : N), g ((Polynomial.X : K[X])^n • x) =
      (T (d*n) : K[T;T⁻¹]) • g x) :
    g.range ≤ Submodule.span K (Set.range (fun j : ι × ℕ =>
      (T (d*j.2) : K[T;T⁻¹]) • g (s j.1))) := by
  classical
  rintro _ ⟨x,rfl⟩
  obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp
    (show x ∈ Submodule.span K[X] (Set.range s) from hs ▸ trivial)
  rw [← hf, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [← Polynomial.sum_C_mul_X_pow_eq (f i), Polynomial.sum, Finset.sum_smul, map_sum]
  apply Submodule.sum_mem
  intro n hn
  rw [mul_smul, ← Polynomial.algebraMap_eq, algebraMap_smul, map_smul, hpow]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i,n),rfl⟩)

theorem range_intersection_finite [Module.Finite K[X] N]
    {P : Type*} [AddCommGroup P] [Module K P] [Module K[X] P]
    [IsScalarTower K K[X] P] [Module.Finite K[X] P]
    [Module.Finite K[T;T⁻¹] Q]
    (f : N →ₗ[K] Q) (g : P →ₗ[K] Q)
    (hf : ∀ x, f ((Polynomial.X : K[X]) • x) = (T 1 : K[T;T⁻¹]) • f x)
    (hg : ∀ x, g ((Polynomial.X : K[X]) • x) = (T (-1) : K[T;T⁻¹]) • g x) :
    Module.Finite K ↥(f.range ⊓ g.range) := by
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := K[X]) (M := N)
  obtain ⟨m,t,ht⟩ := Module.Finite.exists_fin (R := K[X]) (M := P)
  have hp (j : ℕ) (x : N) : f ((Polynomial.X : K[X])^j • x) =
      (T (1*(j : ℤ)) : K[T;T⁻¹]) • f x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_smul, hf, ih, ← mul_smul, ← T_add]
      congr 2
      omega
  have hn (j : ℕ) (x : P) : g ((Polynomial.X : K[X])^j • x) =
      (T ((-1)*(j : ℤ)) : K[T;T⁻¹]) • g x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_smul, hg, ih, ← mul_smul, ← T_add]
      congr 2
      omega
  apply intersection_finite_general f.range g.range (fun i => f (s i)) (fun i => g (t i))
  · simpa only [one_mul] using range_le_lattice s hs f 1 hp
  · simpa only [neg_one_mul] using range_le_lattice t ht g (-1) hn
end
end MaximalSeshadri.LaurentLattices
end


end
end

end OAI
