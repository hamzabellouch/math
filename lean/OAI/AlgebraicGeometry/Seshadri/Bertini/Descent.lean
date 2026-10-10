import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.CountableSpecialization

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

def doubleBaseChange {R K A : Type*} [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] :
    (K ⊗[R] (A ⊗[R] A)) ≃ₐ[K] ((K ⊗[R] A) ⊗[K] (K ⊗[R] A)) :=
  (Algebra.TensorProduct.assoc R R K K A A).symm.trans
    (Algebra.TensorProduct.cancelBaseChange R K K (K ⊗[R] A) A).symm

@[simp] lemma doubleBaseChange_tmul {R K A : Type*} [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] (k : K) (a b : A) :
    (doubleBaseChange (R := R) (K := K) (A := A)) (k ⊗ₜ[R] (a ⊗ₜ[R] b)) =
      (k ⊗ₜ[R] a) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b) := by
  simp [doubleBaseChange]

lemma faithfullyFlat_dvd_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (a b : R) :
    algebraMap R S a ∣ algebraMap R S b ↔ a ∣ b := by
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (Ideal.span {a})
  have hm := congrArg (fun I : Ideal R => b ∈ I) h
  simpa only [Ideal.mem_comap, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] using (Iff.of_eq hm)

theorem scalar_regular_pair_descent {R K A : Type*} [Field R] [Field K] [Algebra R K]
    [CommRing A] [Algebra R A] (a b : A)
    (hab : ∀ t : K ⊗[R] A, (1 : K) ⊗ₜ[R] a ∣ ((1 : K) ⊗ₜ[R] b) * t →
      (1 : K) ⊗ₜ[R] a ∣ t) :
    ∀ t : A, a ∣ b * t → a ∣ t := by
  intro t ht
  let e := Algebra.TensorProduct.comm R A K
  apply (faithfullyFlat_dvd_iff (S := A ⊗[R] K) a t).mp
  change a ⊗ₜ[R] (1 : K) ∣ t ⊗ₜ[R] (1 : K)
  apply (map_dvd_iff e).mp
  simp only [e, Algebra.TensorProduct.comm_tmul]
  apply hab
  obtain ⟨u, hu⟩ := ht
  refine ⟨(1 : K) ⊗ₜ[R] u, ?_⟩
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hu]

lemma scalar_model_injective {R K A : Type*} [Field R] [Field K] [Algebra R K]
    [CommRing A] [Algebra R A] :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective A

theorem model_line_conditions {R K A A₀ : Type*} [Field R] [Field K] [Algebra R K]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [IsDomain A] [IsDomain (A ⊗[K] A)] [CommRing A₀] [Algebra R A₀]
    (e : (K ⊗[R] A₀) ≃ₐ[K] A) (a₀ b₀ : A₀) (a b : A)
    (hea : e (1 ⊗ₜ[R] a₀) = a) (heb : e (1 ⊗ₜ[R] b₀) = b)
    (hb : Transcendental K b)
    (ha : a ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] a ≠ 0)
    (hab : ∀ r : A ⊗[K] A,
      (a ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] a) ∣
        (b ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] b) * r →
      (a ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] a) ∣ r) :
    IsDomain A₀ ∧ IsDomain (A₀ ⊗[R] A₀) ∧ Transcendental R b₀ ∧
      (a₀ ⊗ₜ[R] (1 : A₀) - (1 : A₀) ⊗ₜ[R] a₀ ≠ 0) ∧
      (∀ r : A₀ ⊗[R] A₀,
        (a₀ ⊗ₜ[R] (1 : A₀) - (1 : A₀) ⊗ₜ[R] a₀) ∣
          (b₀ ⊗ₜ[R] (1 : A₀) - (1 : A₀) ⊗ₜ[R] b₀) * r →
        (a₀ ⊗ₜ[R] (1 : A₀) - (1 : A₀) ⊗ₜ[R] a₀) ∣ r) := by
  let g : A₀ →ₐ[R] A := (e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hg : Function.Injective g := e.injective.comp scalar_model_injective
  let eD := (doubleBaseChange (R := R) (K := K) (A := A₀)).trans
    (Algebra.TensorProduct.congr e e)
  have hd (x : A₀) :
      eD ((1 : K) ⊗ₜ[R] (x ⊗ₜ[R] (1 : A₀) - (1 : A₀) ⊗ₜ[R] x)) =
        g x ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] g x := by
    simp only [TensorProduct.tmul_sub, map_sub, eD, AlgEquiv.trans_apply,
      doubleBaseChange_tmul, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom]
    have he1 : e ((1 : K) ⊗ₜ[R] (1 : A₀)) = 1 := e.map_one
    rw [he1]
    rfl
  have hga : g a₀ = a := hea
  have hgb : g b₀ = b := heb
  have hdom : IsDomain (A₀ ⊗[R] A₀) := by
    let : IsDomain (K ⊗[R] (A₀ ⊗[R] A₀)) := eD.injective.isDomain eD.toRingHom
    exact scalar_model_injective.isDomain
      (Algebra.TensorProduct.includeRight : A₀ ⊗[R] A₀ →ₐ[R] K ⊗[R] (A₀ ⊗[R] A₀)).toRingHom
  refine ⟨hg.isDomain g.toRingHom, hdom, ?_, ?_, ?_⟩
  · intro h
    apply hb
    rw [← hgb]
    exact (IsAlgebraic.algHom g h).tower_top K
  · intro hz
    apply ha
    rw [← hga, ← hd, hz, TensorProduct.tmul_zero, map_zero]
  · apply scalar_regular_pair_descent (R := R) (K := K)
    intro t ht
    apply (map_dvd_iff eD).mp
    rw [hd, hga]
    apply hab
    have hh := map_dvd eD ht
    simpa only [map_mul, hd, hga, hgb] using hh

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra
                                                                                               
theorem domain_hyperplane_equation_transport {R K A A₀ σ : Type*}
    [Field R] [Field K] [Algebra R K] [CommRing A] [Algebra K A]
    [CommRing A₀] [Algebra R A₀] [Fintype σ]
    (e : (K ⊗[R] A₀) ≃ₐ[K] A) (v₀ : σ → A₀) (v : σ → A)
    (hv : ∀ i, e (1 ⊗ₜ[R] v₀ i) = v i) (α : σ → K) (β : K)
    [IsDomain ((K ⊗[R] A₀) ⧸ Ideal.span {β ⊗ₜ[R] (1 : A₀) - ∑ i, α i ⊗ₜ[R] v₀ i})] :
    IsDomain (A ⧸ Ideal.span {algebraMap K A β - ∑ i, algebraMap K A (α i) * v i}) := by
  let J : Ideal (K ⊗[R] A₀) := Ideal.span {β ⊗ₜ[R] (1 : A₀) - ∑ i, α i ⊗ₜ[R] v₀ i}
  have he1 (k : K) : e (k ⊗ₜ[R] (1 : A₀)) = algebraMap K A k := e.commutes k
  have het (i : σ) : e (α i ⊗ₜ[R] v₀ i) = algebraMap K A (α i) * v i := by
    have ht : α i ⊗ₜ[R] v₀ i = (α i ⊗ₜ[R] (1 : A₀)) * ((1 : K) ⊗ₜ[R] v₀ i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [ht, map_mul, he1, hv]
  let J' : Ideal A := Ideal.span {algebraMap K A β - ∑ i, algebraMap K A (α i) * v i}
  have hJ : J' = J.map e.toRingHom := by
    change Ideal.span {_} = (Ideal.span {_}).map e.toRingHom
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    change _ = {e (β ⊗ₜ[R] (1 : A₀) - ∑ i, α i ⊗ₜ[R] v₀ i)}
    rw [map_sub, map_sum, he1]
    simp only [het]
  let eQ := Ideal.quotientEquivAlg J J' e hJ
  exact eQ.symm.injective.isDomain eQ.symm.toRingHom

theorem integral_hyperplane_section_over_model {R K A A₀ σ : Type}
    [Field R] [Countable R] [CharZero R] [Field K] [CharZero K]
    [Algebra R K] [IsAlgClosed K] [Uncountable K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra R A]
    [IsScalarTower R K A] [IsDomain (A ⊗[K] A)]
    [CommRing A₀] [Algebra R A₀] [Fintype σ]
    (e : (K ⊗[R] A₀) ≃ₐ[K] A) (v₀ : σ → A₀) (v : σ → A)
    (hv : ∀ i, e (1 ⊗ₜ[R] v₀ i) = v i)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A))
    (i j : σ) (hji : j ≠ i) (hj : Transcendental K (v j))
    (hi : v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i ≠ 0)
    (hij : ∀ r : A ⊗[K] A,
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣
        (v j ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v j) * r →
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣ r) :
    ∃ f : (MvPolynomial σ R)[X] →ₐ[R] K, Function.Injective f ∧
      IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
        ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) := by
  obtain ⟨hA₀, hD₀, _, hi₀, hij₀⟩ := model_line_conditions (R := R) (K := K)
    (A := A) (A₀ := A₀) e (v₀ i) (v₀ j) (v i) (v j) (hv i) (hv j) hj hi hij
  let : IsDomain A₀ := hA₀
  let : IsDomain (A₀ ⊗[R] A₀) := hD₀
  let g : A₀ →ₐ[R] A := (e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hdom₀ := hyperplane_injective_descent (R := R) (K := K) (A := A) (A₀ := A₀)
    g v₀ v hv hdom
  obtain ⟨f, hf, hd⟩ := countable_hyperplane_integral_equation (R := R) (K := K)
    (A := A₀) v₀ hdom₀ i j hji hi₀ hij₀
  let := hd
  exact ⟨f, hf, domain_hyperplane_equation_transport (R := R) (K := K) (A := A)
    (A₀ := A₀) e v₀ v hv (fun k => f (C (MvPolynomial.X k))) (f X)⟩

theorem integral_hyperplane_section {K A : Type} {n : ℕ}
    [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    [IsDomain (A ⊗[K] A)] (v : Fin n → A)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial (Fin n) K)[X] →ₐ[MvPolynomial (Fin n) K] MvPolynomial (Fin n) A))
    (i j : Fin n) (hji : j ≠ i) (hj : Transcendental K (v j))
    (hi : v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i ≠ 0)
    (hij : ∀ r : A ⊗[K] A,
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣
        (v j ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v j) * r →
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣ r)
    (c : Set K) (hc : c.Countable) :
    ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
      ∃ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f ∧
        IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
          ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) := by
  classical
  obtain ⟨S, hS, hcS, m, I, e, v₀, hv⟩ := countable_model_with_elements v c hc
  let : Countable S := hS
  let A₀ := MvPolynomial (Fin m) S ⧸ I
  obtain ⟨f, hf, hd⟩ := integral_hyperplane_section_over_model (R := S) (K := K)
    (A := A) (A₀ := A₀) e v₀ v hv hdom i j hji hj hi hij
  exact ⟨S, hS, hcS, f, hf, hd⟩

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem etale_integral_hyperplane_section {K A ι : Type} {n : ℕ} [Field K] [CharZero K]
    [IsAlgClosed K] [Uncountable K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A]
    [Algebra (MvPolynomial ι K) A] [IsScalarTower K (MvPolynomial ι K) A]
    [Algebra.Etale (MvPolynomial ι K) A]
    (v : Fin n → A) (i j : Fin n) (a b : ι) (hab : a ≠ b)
    (hvi : v i = algebraMap (MvPolynomial ι K) A (MvPolynomial.X a))
    (hvj : v j = algebraMap (MvPolynomial ι K) A (MvPolynomial.X b)) (c : Set K) (hc : c.Countable) :
    ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
      ∃ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f ∧
        IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
          ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) := by
  classical
  let : IsDomain (A ⊗[K] A) := tensorProduct_isDomain_general
  let φ : MvPolynomial ι K →ₐ[K] A := IsScalarTower.toAlgHom K (MvPolynomial ι K) A
  have hφ : φ.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  obtain ⟨hr, hreg⟩ := chartDifference_regular_pair φ hφ a b hab
  let δ : Derivation K A A :=
    (etaleCotangentCoordinate (K := K) (A := A) a).compDer (KaehlerDifferential.D K A)
  have hδi : δ (v i) = 1 := by
    rw [hvi]
    simp [δ]
  have hδj : δ (v j) = 0 := by
    rw [hvj]
    change etaleCotangentCoordinate a
      (KaehlerDifferential.D K A (algebraMap (MvPolynomial ι K) A (MvPolynomial.X b))) = 0
    simp [hab.symm]
  have hji : j ≠ i := by
    rintro rfl
    exact one_ne_zero (hδi.symm.trans hδj)
  let δb : Derivation K A A :=
    (etaleCotangentCoordinate (K := K) (A := A) b).compDer (KaehlerDifferential.D K A)
  have hδb : δb (v j) = 1 := by
    rw [hvj]
    simp [δb]
  have hj : Transcendental K (v j) := transcendental_iff_injective.mpr
    (aeval_injective_of_derivation (FaithfulSMul.algebraMap_injective K A)
      δb (v j) (hδb ▸ one_ne_zero))
  apply integral_hyperplane_section v
    (hyperplane_aeval_injective v δ i (hδi ▸ one_ne_zero)) i j hji hj
  · rw [hvi]
    intro hz
    have hz' : φ (MvPolynomial.X a) ⊗ₜ[K] (1 : A) -
        (1 : A) ⊗ₜ[K] φ (MvPolynomial.X a) = 0 := hz
    have : (1 : A ⊗[K] A) = 0 := hr (by rw [hz']; simp)
    exact one_ne_zero this
  · simpa only [hvi, hvj, φ, IsScalarTower.coe_toAlgHom'] using hreg
  · exact hc

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem hyperplane_integral_fiber_of_injective {R K A σ : Type}
    [Field R] [CharZero R] [Field K] [Algebra R K]
    [CommRing A] [IsDomain A] [Algebra R A] [Fintype σ]
    [IsDomain (A ⊗[R] A)] (v : σ → A)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial σ R)[X] →ₐ[MvPolynomial σ R] MvPolynomial σ A))
    (i j : σ) (hji : j ≠ i)
    (hi : v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i ≠ 0)
    (hij : ∀ r : A ⊗[R] A,
      (v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i) ∣
        (v j ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v j) * r →
      (v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i) ∣ r)
    (f : (MvPolynomial σ R)[X] →ₐ[R] K) (hf : Function.Injective f) :
    let := hyperplaneFamilyAlgebra (K := R) v
    let := f.toRingHom.toAlgebra
    IsDomain (K ⊗[(MvPolynomial σ R)[X]] MvPolynomial σ A) := by
  let := hyperplaneFamilyAlgebra (K := R) v
  let P := (MvPolynomial σ R)[X]
  let : Algebra P K := f.toRingHom.toAlgebra
  let F := FractionRing P
  let g : F →+* K := IsFractionRing.lift (g := f.toRingHom) hf
  let : Algebra F K := g.toAlgebra
  let : IsScalarTower P F K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap hf x).symm
  let : IsDomain ((F ⊗[P] MvPolynomial σ A) ⊗[F] K) :=
    hyperplaneFamily_geometricGeneric_of_injective (E := K) v hdom i j hji hi hij
  let e₁ := Algebra.TensorProduct.comm F K (F ⊗[P] MvPolynomial σ A)
  let : IsDomain (K ⊗[F] (F ⊗[P] MvPolynomial σ A)) := e₁.injective.isDomain e₁.toRingHom
  let e := Algebra.TensorProduct.cancelBaseChange P F K K (MvPolynomial σ A)
  exact e.symm.injective.isDomain e.symm.toRingHom

theorem hyperplane_integral_equation_of_injective {R K A σ : Type}
    [Field R] [CharZero R] [Field K] [Algebra R K]
    [CommRing A] [IsDomain A] [Algebra R A] [Fintype σ]
    [IsDomain (A ⊗[R] A)] (v : σ → A)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial σ R)[X] →ₐ[MvPolynomial σ R] MvPolynomial σ A))
    (i j : σ) (hji : j ≠ i)
    (hi : v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i ≠ 0)
    (hij : ∀ r : A ⊗[R] A,
      (v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i) ∣
        (v j ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v j) * r →
      (v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i) ∣ r)
    (f : (MvPolynomial σ R)[X] →ₐ[R] K) (hf : Function.Injective f) :
    IsDomain ((K ⊗[R] A) ⧸ Ideal.span {f X ⊗ₜ[R] (1 : A) -
      ∑ k, f (C (MvPolynomial.X k)) ⊗ₜ[R] v k}) := by
  let := hyperplaneFamilyAlgebra (K := R) v
  let P := (MvPolynomial σ R)[X]
  let : Algebra P K := f.toRingHom.toAlgebra
  let f₁ : MvPolynomial σ R →ₐ[R] K := f.comp Polynomial.CAlgHom
  let : Algebra (MvPolynomial σ R) K := f₁.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial σ R) K :=
    IsScalarTower.of_algebraMap_eq fun s => (f₁.commutes s).symm
  let : IsScalarTower (MvPolynomial σ R) P K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsDomain (K ⊗[P] MvPolynomial σ A) :=
    hyperplane_integral_fiber_of_injective v hdom i j hji hi hij f hf
  obtain ⟨q⟩ := hyperplane_specialization_equiv (R := R) (K := K) v
  exact q.symm.injective.isDomain q.symm.toRingHom

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
