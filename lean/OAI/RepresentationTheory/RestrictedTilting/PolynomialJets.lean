import OAI.RepresentationTheory.RestrictedTilting.JetTriviality

namespace OAI

namespace FiberFunctorProof
open scoped TensorProduct
universe u
variable {k : Type u} [Field k]
variable {T N : Type u} [AddCommGroup T] [Module k T]
  [AddCommGroup N] [Module k N]
  [Module (MvPolynomial (Fin 2) k) N] [IsScalarTower k (MvPolynomial (Fin 2) k) N]

noncomputable def polynomialExtend (L : T →ₗ[k] N) :
    (MvPolynomial (Fin 2) k) ⊗[k] T →ₗ[MvPolynomial (Fin 2) k] N :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton (MvPolynomial (Fin 2) k) (T →ₗ[k] N) L)

@[simp] lemma polynomialExtend_tmul (L : T →ₗ[k] N)
    (P : MvPolynomial (Fin 2) k) (t : T) :
    polynomialExtend L (P ⊗ₜ[k] t) = P • L t := rfl

noncomputable def polynomialAugment : (MvPolynomial (Fin 2) k) ⊗[k] T →ₗ[k] T :=
  (TensorProduct.lid k T).toLinearMap ∘ₗ TensorProduct.map
    ({ toFun := MvPolynomial.constantCoeff
       map_add' := map_add _
       map_smul' := MvPolynomial.constantCoeff_smul } : MvPolynomial (Fin 2) k →ₗ[k] k)
    LinearMap.id

@[simp] lemma polynomialAugment_tmul (P : MvPolynomial (Fin 2) k) (t : T) :
    polynomialAugment (P ⊗ₜ[k] t) = MvPolynomial.constantCoeff P • t := rfl

lemma polynomialAugment_smul (P : MvPolynomial (Fin 2) k)
    (z : (MvPolynomial (Fin 2) k) ⊗[k] T) :
    polynomialAugment (P • z) = MvPolynomial.constantCoeff P • polynomialAugment z := by
  induction z using TensorProduct.inductionOn with
  | tmul Q t => rw [TensorProduct.smul_tmul', polynomialAugment_tmul]; simp [smul_eq_mul, mul_smul]
  | add z w hz hw => simp [smul_add, hz, hw]

lemma polynomialAugment_pairRelation
    (z : (MvPolynomial (Fin 2) k) ⊗[k] T)
    (hz : z ∈ pairRelation (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1)) :
    polynomialAugment z = 0 := by
  obtain ⟨a,b,rfl⟩ := (mem_pairRelation _ _ z).mp hz
  simp [polynomialAugment_smul]

lemma polynomial_origin_representative (z : (MvPolynomial (Fin 2) k) ⊗[k] T) :
    z - (1 : MvPolynomial (Fin 2) k) ⊗ₜ[k] polynomialAugment z ∈
      pairRelation (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) := by
  let Q := (pairRelation (M := (MvPolynomial (Fin 2) k) ⊗[k] T)
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1)).restrictScalars k
  suffices h : Q.mkQ z = Q.mkQ (1 ⊗ₜ[k] polynomialAugment z) by
    exact (Submodule.Quotient.mk_eq_zero Q).mp (by change Q.mkQ (z - 1 ⊗ₜ[k] polynomialAugment z) = 0; rw [map_sub, h, sub_self])
  induction z using TensorProduct.inductionOn with
  | tmul P t =>
    have hX : ∀ (i : Fin 2) (m : (MvPolynomial (Fin 2) k) ⊗[k] T),
        (MvPolynomial.X i : MvPolynomial (Fin 2) k) • m ∈ Q := by
      intro i m
      fin_cases i
      · exact x_smul_mem_pairRelation _ _ m
      · exact y_smul_mem_pairRelation _ _ m
    have hh := originQuotient_polynomial_smul Q hX P (1 ⊗ₜ[k] t)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at hh
    rw [polynomialAugment_tmul, TensorProduct.tmul_smul, map_smul]
    exact hh
  | add z w hz hw => simp [map_add, TensorProduct.tmul_add, hz, hw]

 

theorem polynomialExtend_jet_bijective (q : N →ₗ[k] T) (L : T →ₗ[k] N)
    (hq : ∀ n, q n = 0 ↔ n ∈ pairRelation (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1))
    (hL : q ∘ₗ L = LinearMap.id)
    (hx : Function.Injective (fun n : N => (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • n))
    (hy : ∀ v n : N, (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) • v =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • n →
      ∃ w, v = (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • w) (j : ℕ) :
    Function.Bijective (jetMap (polynomialExtend L) (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) j) := by
  have hqL : ∀ t, q (L t) = t := fun t => congrArg (fun f : T →ₗ[k] T => f t) hL
  have hqX : ∀ i n, q ((MvPolynomial.X i : MvPolynomial (Fin 2) k) • n) = 0 := by
    intro i n
    apply (hq _).mpr
    fin_cases i
    · exact x_smul_mem_pairRelation _ _ n
    · exact y_smul_mem_pairRelation _ _ n
  have hqP : ∀ P n, q ((P : MvPolynomial (Fin 2) k) • n) = MvPolynomial.constantCoeff P • q n := by
    intro P n
    induction P using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.constantCoeff_C]
      change q (algebraMap k (MvPolynomial (Fin 2) k) a • n) = a • q n
      rw [algebraMap_smul, map_smul]
    | add P Q hP hQ => simp only [add_smul, map_add, hP, hQ]
    | mul_X P i _ => rw [mul_comm, mul_smul, hqX]; simp
  have he : ∀ z, q (polynomialExtend L z) = polynomialAugment z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul P t => simp [hqP, hqL]
    | add z w hz hw => simp [hz, hw]
  constructor
  · apply jetMap_injective (polynomialExtend L) _ _ hx hy
    intro z hz
    have hzero : polynomialAugment z = 0 := (he z).symm.trans ((hq _).mpr hz)
    simpa only [hzero, TensorProduct.tmul_zero, sub_zero] using polynomial_origin_representative z
  · apply jetMap_surjective
    intro n
    refine ⟨1 ⊗ₜ[k] q n, (hq _).mp ?_⟩
    simp [hqL]
end FiberFunctorProof

end OAI
