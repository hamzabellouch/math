import Mathlib

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.LaurentLattices
noncomputable section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]

instance : IsPrincipalIdealRing K[T;T⁻¹] where
  principal I := by
    obtain ⟨a,ha⟩ := (IsPrincipalIdealRing.principal (I.under K[X])).principal
    refine ⟨⟨algebraMap K[X] K[T;T⁻¹] a, ?_⟩⟩
    rw [← IsLocalization.map_under (Submonoid.powers (Polynomial.X : K[X]))
      K[T;T⁻¹] I, ha, Ideal.map_span, Set.image_singleton]

def boundedBelow {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M]
    (b : Basis ι K[T;T⁻¹] M) (l : ℤ) : Submodule K M :=
  ⨅ i, (AddMonoidAlgebra.supported K K (Set.Ici l)).comap
    (((Finsupp.lapply i).comp b.repr.toLinearMap).restrictScalars K)

def boundedAbove {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M]
    (b : Basis ι K[T;T⁻¹] M) (u : ℤ) : Submodule K M :=
  ⨅ i, (AddMonoidAlgebra.supported K K (Set.Iic u)).comap
    (((Finsupp.lapply i).comp b.repr.toLinearMap).restrictScalars K)

variable {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
  [Module K M] [IsScalarTower K K[T;T⁻¹] M]

lemma mem_boundedBelow (b : Basis ι K[T;T⁻¹] M) (l : ℤ) (x : M) :
    x ∈ boundedBelow b l ↔ ∀ i z, z < l → ((b.repr x) i).coeff z = 0 := by
  simp only [boundedBelow, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Finsupp.lapply_apply, AddMonoidAlgebra.mem_supported',
    Set.mem_Ici, not_le]

lemma mem_boundedAbove (b : Basis ι K[T;T⁻¹] M) (u : ℤ) (x : M) :
    x ∈ boundedAbove b u ↔ ∀ i z, u < z → ((b.repr x) i).coeff z = 0 := by
  simp only [boundedAbove, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Finsupp.lapply_apply, AddMonoidAlgebra.mem_supported',
    Set.mem_Iic, not_le]

lemma coeff_T_mul (p : K[T;T⁻¹]) (n z : ℤ) :
    (T n * p).coeff z = p.coeff (z-n) := by
  simp only [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  congr 1
  omega

lemma below_shift (b : Basis ι K[T;T⁻¹] M) (l : ℤ) {x : M}
    (hx : x ∈ boundedBelow b l) (n : ℕ) :
    (T (n : ℤ) : K[T;T⁻¹]) • x ∈ boundedBelow b l := by
  rw [mem_boundedBelow] at hx ⊢
  intro i z hz
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, coeff_T_mul]
  exact hx i _ (by omega)

lemma above_shift (b : Basis ι K[T;T⁻¹] M) (u : ℤ) {x : M}
    (hx : x ∈ boundedAbove b u) (n : ℕ) :
    (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ boundedAbove b u := by
  rw [mem_boundedAbove] at hx ⊢
  intro i z hz
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, coeff_T_mul]
  exact hx i _ (by omega)

theorem band_finite [Fintype ι] (b : Basis ι K[T;T⁻¹] M) (l u : ℤ) :
    Module.Finite K ↥(boundedBelow b l ⊓ boundedAbove b u) := by
  classical
  let W := boundedBelow b l ⊓ boundedAbove b u
  let J := ι × ↥(Finset.Icc l u)
  let φ : W →ₗ[K] (J → K) := LinearMap.pi (fun j =>
    (Finsupp.lapply j.2.val).comp ((AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap.comp
      ((((Finsupp.lapply j.1).comp b.repr.toLinearMap).restrictScalars K).comp W.subtype)))
  apply Module.Finite.of_injective φ
  intro x y hxy
  apply Subtype.ext
  apply b.repr.injective
  ext i z
  by_cases hzL : z < l
  · rw [(mem_boundedBelow b l x.val).mp x.property.1 i z hzL,
      (mem_boundedBelow b l y.val).mp y.property.1 i z hzL]
  · by_cases hzU : u < z
    · rw [(mem_boundedAbove b u x.val).mp x.property.2 i z hzU,
        (mem_boundedAbove b u y.val).mp y.property.2 i z hzU]
    · exact congrFun hxy (i,⟨z,Finset.mem_Icc.mpr (by omega)⟩)

lemma finite_generators_bounded [Fintype ι] {κ : Type*} [Fintype κ]
    (b : Basis ι K[T;T⁻¹] M) (s : κ → M) :
    ∃ l u : ℤ, ∀ j, s j ∈ boundedBelow b l ∧ s j ∈ boundedAbove b u := by
  classical
  let S : Set ℤ := ⋃ i, ⋃ j, (↑((b.repr (s j)) i).coeff.support : Set ℤ)
  have hS : S.Finite := Set.finite_iUnion fun i => Set.finite_iUnion fun j =>
    Finset.finite_toSet _
  obtain ⟨l,hl⟩ := hS.bddBelow
  obtain ⟨u,hu⟩ := hS.bddAbove
  refine ⟨l,u,fun j => ⟨?_,?_⟩⟩
  · rw [mem_boundedBelow]
    intro i z hz
    by_contra hn
    have hm : z ∈ S := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
      ⟨j,Finsupp.mem_support_iff.mpr hn⟩⟩
    exact (not_le.mpr hz) (hl hm)
  · rw [mem_boundedAbove]
    intro i z hz
    by_contra hn
    have hm : z ∈ S := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
      ⟨j,Finsupp.mem_support_iff.mpr hn⟩⟩
    exact (not_le.mpr hz) (hu hm)

theorem intersection_finite [Module.Finite K[T;T⁻¹] M]
    [Module.IsTorsionFree K[T;T⁻¹] M]
    (A B : Submodule K M) {κ τ : Type*} [Fintype κ] [Fintype τ]
    (s : κ → M) (t : τ → M)
    (hA : A ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • s j.1)))
    (hB : B ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • t j.1))) :
    Module.Finite K ↥(A ⊓ B) := by
  let b := Module.Free.chooseBasis K[T;T⁻¹] M
  obtain ⟨l,_,hs⟩ := finite_generators_bounded b s
  obtain ⟨_,u,ht⟩ := finite_generators_bounded b t
  have hbelow : A ≤ boundedBelow b l := hA.trans (Submodule.span_le.mpr (by
    rintro _ ⟨⟨j,n⟩,rfl⟩
    exact below_shift b l (hs j).1 n))
  have habove : B ≤ boundedAbove b u := hB.trans (Submodule.span_le.mpr (by
    rintro _ ⟨⟨j,n⟩,rfl⟩
    exact above_shift b u (ht j).2 n))
  let := band_finite b l u
  exact Module.Finite.of_injective (Submodule.inclusion (inf_le_inf hbelow habove))
    (Submodule.inclusion_injective _)

end
end MaximalSeshadri.LaurentLattices
end


end
end

end OAI
