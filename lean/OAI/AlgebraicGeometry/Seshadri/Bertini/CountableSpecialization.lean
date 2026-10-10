import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.EtaleCoordinates

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Cardinal

theorem field_embedding_over_countable {R F K : Type} [Field R] [Countable R]
    [Field F] [Field K] [Algebra R F] [Algebra R K] [IsAlgClosed K]
    [Uncountable K] (hcard : #F ≤ #K) : Nonempty (F →ₐ[R] K) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R F
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R K
  have hK : #K = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
      (Subtype.val : t → K) ht Cardinal.mk_le_aleph0 Cardinal.aleph0_lt_mk
  have hst : #s ≤ #t := (Cardinal.mk_subtype_le s).trans (hcard.trans_eq hK)
  obtain ⟨e⟩ := (Cardinal.le_def s t).mp hst
  let w : s → K := fun i => (e i : K)
  have hw : AlgebraicIndependent R w := ht.1.comp e e.injective
  let B := Algebra.adjoin R (Set.range (Subtype.val : s → F))
  let f : B →ₐ[R] K := (MvPolynomial.aeval w).comp hs.1.aevalEquiv.symm.toAlgHom
  have hf : Function.Injective f :=
    (algebraicIndependent_iff_injective_aeval.mp hw).comp hs.1.aevalEquiv.symm.injective
  let : Algebra B K := f.toRingHom.toAlgebra
  let : IsScalarTower R B K := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  let : Module.IsTorsionFree B K := Module.isTorsionFree_iff_algebraMap_injective.mpr hf
  let : Algebra.IsAlgebraic B F := hs.isAlgebraic
  exact ⟨(IsAlgClosed.lift : F →ₐ[B] K).restrictScalars R⟩

theorem generic_field_embedding {R K : Type} [Field R] [Countable R]
    [Field K] [Algebra R K] [IsAlgClosed K] [Uncountable K]
    (n : Type) [Finite n] :
    Nonempty (FractionRing (MvPolynomial n K) →ₐ[R] K) := by
  apply field_embedding_over_countable
  rw [Cardinal.mk_fractionRing]
  exact MvPolynomial.cardinalMk_le_max.trans (by
    simp only [max_le_iff]
    exact ⟨⟨le_rfl, Cardinal.mk_le_aleph0.trans (le_of_lt Cardinal.aleph0_lt_mk)⟩,
      le_of_lt Cardinal.aleph0_lt_mk⟩)

open scoped TensorProduct

theorem integral_specialization_of_countable_model
    {R F K P B : Type} [Field R] [Countable R] [Field F] [Field K]
    [Algebra R F] [Algebra R K] [IsAlgClosed K] [Uncountable K]
    [CommRing P] [Algebra R P] [Algebra P F] [IsScalarTower R P F]
    [CommRing B] [Algebra P B]
    (hcard : Cardinal.mk F ≤ Cardinal.mk K)
    (hinj : Function.Injective (algebraMap P F))
    (hgeo : ∀ (E : Type) [Field E] [Algebra F E],
      IsDomain (E ⊗[F] (F ⊗[P] B))) :
    ∃ f : P →ₐ[R] K, Function.Injective f ∧
      (let := f.toRingHom.toAlgebra
       IsDomain (K ⊗[P] B)) := by
  obtain ⟨φ⟩ := field_embedding_over_countable (R := R) hcard
  let f : P →ₐ[R] K := φ.comp (IsScalarTower.toAlgHom R P F)
  let : Algebra F K := φ.toRingHom.toAlgebra
  let : Algebra P K := f.toRingHom.toAlgebra
  let : IsScalarTower P F K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsDomain (K ⊗[F] (F ⊗[P] B)) := hgeo K
  refine ⟨f, φ.injective.comp hinj, ?_⟩
  let e := Algebra.TensorProduct.cancelBaseChange P F K K B
  exact e.symm.injective.isDomain e.symm.toRingHom

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem countable_etale_hyperplane_integral_equation {R K A σ ι : Type}
    [Field R] [CharZero R] [Countable R] [IsAlgClosed R]
    [Field K] [Algebra R K] [IsAlgClosed K] [Uncountable K]
    [CommRing A] [IsDomain A] [Algebra R A] [Fintype σ]
    [Algebra (MvPolynomial ι R) A] [IsScalarTower R (MvPolynomial ι R) A]
    [Algebra.Etale (MvPolynomial ι R) A]
    (v : σ → A) (i j : σ) (a b : ι) (hab : a ≠ b)
    (hvi : v i = algebraMap (MvPolynomial ι R) A (MvPolynomial.X a))
    (hvj : v j = algebraMap (MvPolynomial ι R) A (MvPolynomial.X b)) :
    ∃ f : (MvPolynomial σ R)[X] →ₐ[R] K, Function.Injective f ∧
      IsDomain ((K ⊗[R] A) ⧸ Ideal.span {f X ⊗ₜ[R] (1 : A) -
        ∑ k, f (C (MvPolynomial.X k)) ⊗ₜ[R] v k}) := by
  let P := (MvPolynomial σ R)[X]
  let F := FractionRing P
  let := hyperplaneFamilyAlgebra (K := R) v
  have hgeo (E : Type) [Field E] [Algebra F E] :
      IsDomain (E ⊗[F] (F ⊗[P] MvPolynomial σ A)) := by
    let : IsDomain ((F ⊗[P] MvPolynomial σ A) ⊗[F] E) :=
      etale_hyperplane_geometricGeneric (E := E) v i j a b hab hvi hvj
    let e := Algebra.TensorProduct.comm F E (F ⊗[P] MvPolynomial σ A)
    exact e.injective.isDomain e.toRingHom
  let : Countable (MvPolynomial σ R) := AddMonoidAlgebra.coeff_injective.countable
  let : Countable (AddMonoidAlgebra (MvPolynomial σ R) ℕ) :=
    AddMonoidAlgebra.coeff_injective.countable
  let : Countable P := Polynomial.toFinsupp_injective.countable
  have hcard : Cardinal.mk F ≤ Cardinal.mk K := by
    change Cardinal.mk (FractionRing P) ≤ _
    rw [Cardinal.mk_fractionRing]
    exact Cardinal.mk_le_aleph0.trans (Cardinal.aleph0_lt_mk.le)
  obtain ⟨f, hfinj, hdom⟩ := integral_specialization_of_countable_model
    (R := R) (F := F) (K := K) (P := P) (B := MvPolynomial σ A)
    hcard (IsFractionRing.injective P F) hgeo
  let : Algebra P K := f.toRingHom.toAlgebra
  let f₁ : MvPolynomial σ R →ₐ[R] K := f.comp Polynomial.CAlgHom
  let : Algebra (MvPolynomial σ R) K := f₁.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial σ R) K :=
    IsScalarTower.of_algebraMap_eq fun s => (f₁.commutes s).symm
  let : IsScalarTower (MvPolynomial σ R) P K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsDomain (K ⊗[P] MvPolynomial σ A) := hdom
  obtain ⟨q⟩ := hyperplane_specialization_equiv (R := R) (K := K) v
  exact ⟨f, hfinj, q.symm.injective.isDomain q.symm.toRingHom⟩
end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra
theorem hyperplaneFamily_geometricGeneric_of_injective {K A E σ : Type} [Field K] [CharZero K]
    [CommRing A] [IsDomain A] [Algebra K A] [Fintype σ]
    [IsDomain (A ⊗[K] A)] [Field E]
    [Algebra (FractionRing (MvPolynomial σ K)[X]) E]
    (v : σ → A)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A))
    (i j : σ) (hji : j ≠ i)
    (hi : v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i ≠ 0)
    (hij : ∀ r : A ⊗[K] A,
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣
        (v j ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v j) * r →
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣ r) :
    let := hyperplaneFamilyAlgebra (K := K) v
    IsDomain ((FractionRing (MvPolynomial σ K)[X] ⊗[(MvPolynomial σ K)[X]]
      MvPolynomial σ A) ⊗[FractionRing (MvPolynomial σ K)[X]] E) := by
  let := hyperplaneFamilyAlgebra (K := K) v
  let := hyperplaneFamilyAlgebra_tower (K := K) v
  let : IsDomain (MvPolynomial σ A ⊗[(MvPolynomial σ K)[X]] MvPolynomial σ A) :=
    hyperplaneFamily_double_isDomain v (by change Polynomial.aeval _ X = _; simp) i j hji hi hij
  let : IsDomain (FractionRing (MvPolynomial σ K)[X] ⊗[(MvPolynomial σ K)[X]]
      MvPolynomial σ A) := genericFiber_isDomain hdom
  let : IsDomain ((FractionRing (MvPolynomial σ K)[X] ⊗[(MvPolynomial σ K)[X]]
      MvPolynomial σ A) ⊗[FractionRing (MvPolynomial σ K)[X]]
      (FractionRing (MvPolynomial σ K)[X] ⊗[(MvPolynomial σ K)[X]]
      MvPolynomial σ A)) := doubledGenericFiber_isDomain hdom
  exact self_tensor_domain_geometrically_domain_algebra

theorem countable_hyperplane_integral_equation {R K A σ : Type}
    [Field R] [CharZero R] [Countable R]
    [Field K] [Algebra R K] [IsAlgClosed K] [Uncountable K]
    [CommRing A] [IsDomain A] [Algebra R A] [Fintype σ]
    [IsDomain (A ⊗[R] A)]
    (v : σ → A)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial σ R)[X] →ₐ[MvPolynomial σ R] MvPolynomial σ A))
    (i j : σ) (hji : j ≠ i)
    (hi : v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i ≠ 0)
    (hij : ∀ r : A ⊗[R] A,
      (v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i) ∣
        (v j ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v j) * r →
      (v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i) ∣ r) :
    ∃ f : (MvPolynomial σ R)[X] →ₐ[R] K, Function.Injective f ∧
      IsDomain ((K ⊗[R] A) ⧸ Ideal.span {f X ⊗ₜ[R] (1 : A) -
        ∑ k, f (C (MvPolynomial.X k)) ⊗ₜ[R] v k}) := by
  let P := (MvPolynomial σ R)[X]
  let F := FractionRing P
  let := hyperplaneFamilyAlgebra (K := R) v
  have hgeo (E : Type) [Field E] [Algebra F E] :
      IsDomain (E ⊗[F] (F ⊗[P] MvPolynomial σ A)) := by
    let : IsDomain ((F ⊗[P] MvPolynomial σ A) ⊗[F] E) :=
      hyperplaneFamily_geometricGeneric_of_injective (E := E) v hdom i j hji hi hij
    let e := Algebra.TensorProduct.comm F E (F ⊗[P] MvPolynomial σ A)
    exact e.injective.isDomain e.toRingHom
  let : Countable (MvPolynomial σ R) := AddMonoidAlgebra.coeff_injective.countable
  let : Countable (AddMonoidAlgebra (MvPolynomial σ R) ℕ) :=
    AddMonoidAlgebra.coeff_injective.countable
  let : Countable P := Polynomial.toFinsupp_injective.countable
  have hcard : Cardinal.mk F ≤ Cardinal.mk K := by
    change Cardinal.mk (FractionRing P) ≤ _
    rw [Cardinal.mk_fractionRing]
    exact Cardinal.mk_le_aleph0.trans (Cardinal.aleph0_lt_mk.le)
  obtain ⟨f, hfinj, hdom⟩ := integral_specialization_of_countable_model
    (R := R) (F := F) (K := K) (P := P) (B := MvPolynomial σ A)
    hcard (IsFractionRing.injective P F) hgeo
  let : Algebra P K := f.toRingHom.toAlgebra
  let f₁ : MvPolynomial σ R →ₐ[R] K := f.comp Polynomial.CAlgHom
  let : Algebra (MvPolynomial σ R) K := f₁.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial σ R) K :=
    IsScalarTower.of_algebraMap_eq fun s => (f₁.commutes s).symm
  let : IsScalarTower (MvPolynomial σ R) P K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsDomain (K ⊗[P] MvPolynomial σ A) := hdom
  obtain ⟨q⟩ := hyperplane_specialization_equiv (R := R) (K := K) v
  exact ⟨f, hfinj, q.symm.injective.isDomain q.symm.toRingHom⟩
end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem hyperplane_injective_descent {R K A A₀ σ : Type*}
    [Field R] [Field K] [Algebra R K]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [CommRing A₀] [Algebra R A₀] [Fintype σ]
    (g : A₀ →ₐ[R] A) (v₀ : σ → A₀) (v : σ → A)
    (hv : ∀ i, g (v₀ i) = v i)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A)) :
    Function.Injective (Polynomial.aeval (homogeneousLinearForm v₀) :
      (MvPolynomial σ R)[X] →ₐ[MvPolynomial σ R] MvPolynomial σ A₀) := by
  let G : MvPolynomial σ A₀ →+* MvPolynomial σ A := MvPolynomial.map g.toRingHom
  let U : (MvPolynomial σ R)[X] →+* (MvPolynomial σ K)[X] :=
    Polynomial.mapRingHom (MvPolynomial.map (algebraMap R K))
  let f₀ := (Polynomial.aeval (homogeneousLinearForm v₀) :
    (MvPolynomial σ R)[X] →ₐ[MvPolynomial σ R] MvPolynomial σ A₀)
  let f := (Polynomial.aeval (homogeneousLinearForm v) :
    (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A)
  have hcomp : G.comp f₀.toRingHom = f.toRingHom.comp U := by
    apply Polynomial.ringHom_ext
    · intro p
      change G (f₀ (C p)) = f (U (C p))
      simp only [f₀, f, U, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.aeval_C]
      simp only [MvPolynomial.algebraMap_def, G, MvPolynomial.map_map]
      have hsc : g.toRingHom.comp (algebraMap R A₀) =
          (algebraMap K A).comp (algebraMap R K) := by
        ext r
        exact (g.commutes r).trans (IsScalarTower.algebraMap_apply R K A r)
      exact congrArg (fun h : R →+* A => MvPolynomial.map h p) hsc
    · change G (f₀ X) = f (U X)
      simp only [f₀, f, U, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.aeval_X]
      simp only [G, homogeneousLinearForm, map_sum, map_mul,
        MvPolynomial.map_C, MvPolynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hv]
  have hU : Function.Injective U :=
    Polynomial.map_injective _ (MvPolynomial.map_injective (algebraMap R K) (FaithfulSMul.algebraMap_injective R K))
  intro p q hpq
  apply hU
  apply hdom
  have hp := DFunLike.congr_fun hcomp p
  have hq := DFunLike.congr_fun hcomp q
  change G (f₀ p) = f (U p) at hp
  change G (f₀ q) = f (U q) at hq
  exact hp.symm.trans ((congrArg G hpq).trans hq)
end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

def polynomialQuotientBaseChange {R K n : Type*} [CommRing R] [CommRing K]
    [Algebra R K] (I : Ideal (MvPolynomial n R)) :
    (K ⊗[R] (MvPolynomial n R ⧸ I)) ≃ₐ[K]
      MvPolynomial n K ⧸ I.map (MvPolynomial.map (algebraMap R K)) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := n) R K
  refine (Algebra.TensorProduct.tensorQuotientEquiv K (MvPolynomial n R) K I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change I.map (MvPolynomial.map (algebraMap R K)) =
    (I.map (Algebra.TensorProduct.includeRight : MvPolynomial n R →ₐ[R]
      K ⊗[R] MvPolynomial n R).toRingHom).map e.toRingHom
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  change MvPolynomial.map (algebraMap R K) p = e (1 ⊗ₜ[R] p)
  simp [e]

theorem countable_polynomial_model {K A : Type} [Field K] [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (c : Set K) (hc : c.Countable) :
    ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
      ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) S)),
        Nonempty ((K ⊗[S] (MvPolynomial (Fin n) S ⧸ I)) ≃ₐ[K] A) := by
  classical
  let : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨n, I, e, q, hq⟩ := Algebra.FinitePresentation.iff.mp
    (inferInstance : Algebra.FinitePresentation K A)
  let d : Finset K := q.biUnion MvPolynomial.coeffs
  let S := Subfield.closure (c ∪ (d : Set K))
  have hcount : Countable S := Cardinal.mk_le_aleph0_iff.mp
    ((Subfield.cardinalMk_closure_le_max _).trans (max_le
      ((hc.union d.countable_toSet).le_aleph0) le_rfl))
  refine ⟨S, hcount, fun x hx => Subfield.subset_closure (Or.inl hx), n,
    I.comap (MvPolynomial.map S.subtype), ?_⟩
  have hI : (I.comap (MvPolynomial.map S.subtype)).map (MvPolynomial.map S.subtype) = I := by
    apply le_antisymm Ideal.map_comap_le
    rw [← hq]
    apply Ideal.span_le.mpr
    intro p hp
    have hpS : p ∈ Set.range (MvPolynomial.map S.subtype) := by
      apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
      intro x hx
      refine ⟨⟨x, Subfield.subset_closure (Or.inr ?_)⟩, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨p, hp, hx⟩
    obtain ⟨p₀, rfl⟩ := hpS
    apply Ideal.mem_map_of_mem
    exact Ideal.subset_span hp
  let e₀ := polynomialQuotientBaseChange (K := K) (I.comap (MvPolynomial.map S.subtype))
  exact ⟨e₀.trans ((Ideal.quotientEquivAlgOfEq K hI).trans e)⟩

lemma polynomialQuotientBaseChange_tmul {R K n : Type*} [CommRing R] [CommRing K]
    [Algebra R K] (I : Ideal (MvPolynomial n R)) (p : MvPolynomial n R) :
    polynomialQuotientBaseChange (K := K) I ((1 : K) ⊗ₜ[R] Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R K) p) := by
  simp [polynomialQuotientBaseChange, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]

theorem countable_model_with_elements {K A : Type} [Field K] [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] {k : ℕ} (v : Fin k → A)
    (c : Set K) (hc : c.Countable) :
    ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
      ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) S))
        (e : (K ⊗[S] (MvPolynomial (Fin n) S ⧸ I)) ≃ₐ[K] A)
        (v₀ : Fin k → MvPolynomial (Fin n) S ⧸ I),
        ∀ i, e (1 ⊗ₜ[S] v₀ i) = v i := by
  classical
  let : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨n, I, e, q, hq⟩ := Algebra.FinitePresentation.iff.mp
    (inferInstance : Algebra.FinitePresentation K A)
  have hp : ∀ i, ∃ p : MvPolynomial (Fin n) K, e (Ideal.Quotient.mk I p) = v i := by
    intro i
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (e.symm (v i))
    exact ⟨p, by rw [hp, e.apply_symm_apply]⟩
  choose p hp using hp
  let d : Finset K := (q.biUnion MvPolynomial.coeffs) ∪
    (Finset.univ.biUnion fun i => (p i).coeffs)
  let S := Subfield.closure (c ∪ (d : Set K))
  have hcount : Countable S := Cardinal.mk_le_aleph0_iff.mp
    ((Subfield.cardinalMk_closure_le_max _).trans (max_le
      ((hc.union d.countable_toSet).le_aleph0) le_rfl))
  have lift_poly (f : MvPolynomial (Fin n) K) (hf : f.coeffs ⊆ d) :
      ∃ f₀ : MvPolynomial (Fin n) S, MvPolynomial.map S.subtype f₀ = f := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro x hx
    exact ⟨⟨x, Subfield.subset_closure (Or.inr (hf hx))⟩, rfl⟩
  let I₀ := I.comap (MvPolynomial.map S.subtype)
  have hI : I₀.map (MvPolynomial.map S.subtype) = I := by
    apply le_antisymm Ideal.map_comap_le
    rw [← hq]
    apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨f₀, rfl⟩ := lift_poly f (fun x hx => Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨f, hf, hx⟩))
    apply Ideal.mem_map_of_mem
    exact Ideal.subset_span hf
  have hp₀ : ∀ i, ∃ p₀ : MvPolynomial (Fin n) S, MvPolynomial.map S.subtype p₀ = p i := by
    intro i
    exact lift_poly (p i) (fun x hx => Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩))
  choose p₀ hp₀ using hp₀
  let e₀ := (polynomialQuotientBaseChange (K := K) I₀).trans
    ((Ideal.quotientEquivAlgOfEq K hI).trans e)
  refine ⟨S, hcount, fun x hx => Subfield.subset_closure (Or.inl hx), n, I₀, e₀,
    fun i => Ideal.Quotient.mk I₀ (p₀ i), ?_⟩
  intro i
  change e ((Ideal.quotientEquivAlgOfEq K hI)
    (polynomialQuotientBaseChange I₀ (1 ⊗ₜ[S] Ideal.Quotient.mk I₀ (p₀ i)))) = _
  rw [polynomialQuotientBaseChange_tmul]
  change e ((Ideal.quotientEquivAlgOfEq K hI)
    (Ideal.Quotient.mk _ (MvPolynomial.map S.subtype (p₀ i)))) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rw [hp₀, hp]

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
