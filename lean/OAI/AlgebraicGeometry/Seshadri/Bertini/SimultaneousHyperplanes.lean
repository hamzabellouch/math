import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.Descent

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra
                                                                                    
theorem generic_hyperplane_section_over_model {R K A A₀ σ : Type}
    [Field R] [CharZero R] [Field K] [CharZero K]
    [Algebra R K]
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
    ∀ f : (MvPolynomial σ R)[X] →ₐ[R] K, Function.Injective f →
      IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
        ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) := by
  intro f hf
  obtain ⟨hA₀, hD₀, _, hi₀, hij₀⟩ := model_line_conditions (R := R) (K := K)
    (A := A) (A₀ := A₀) e (v₀ i) (v₀ j) (v i) (v j) (hv i) (hv j) hj hi hij
  let : IsDomain A₀ := hA₀
  let : IsDomain (A₀ ⊗[R] A₀) := hD₀
  let g : A₀ →ₐ[R] A := (e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hdom₀ := hyperplane_injective_descent (R := R) (K := K) (A := A) (A₀ := A₀)
    g v₀ v hv hdom
  let := hyperplane_integral_equation_of_injective (R := R) (K := K)
    (A := A₀) v₀ hdom₀ i j hji hi₀ hij₀ f hf
  exact domain_hyperplane_equation_transport (R := R) (K := K) (A := A)
    (A₀ := A₀) e v₀ v hv (fun k => f (C (MvPolynomial.X k))) (f X)

theorem generic_hyperplane_section {K A : Type} {n : ℕ}
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
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
        IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
          ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) := by
  classical
  obtain ⟨S, hS, hcS, m, I, e, v₀, hv⟩ := countable_model_with_elements v c hc
  let : Countable S := hS
  let A₀ := MvPolynomial (Fin m) S ⧸ I
  refine ⟨S, hS, hcS, ?_⟩
  exact generic_hyperplane_section_over_model (R := S) (K := K)
    (A := A) (A₀ := A₀) e v₀ v hv hdom i j hji hj hi hij

theorem etale_generic_hyperplane_section {K A ι : Type} {n : ℕ} [Field K] [CharZero K]
    [IsAlgClosed K] [Uncountable K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A]
    [Algebra (MvPolynomial ι K) A] [IsScalarTower K (MvPolynomial ι K) A]
    [Algebra.Etale (MvPolynomial ι K) A]
    (v : Fin n → A) (i j : Fin n) (a b : ι) (hab : a ≠ b)
    (hvi : v i = algebraMap (MvPolynomial ι K) A (MvPolynomial.X a))
    (hvj : v j = algebraMap (MvPolynomial ι K) A (MvPolynomial.X b)) (c : Set K) (hc : c.Countable) :
    ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
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
  apply generic_hyperplane_section v
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
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra
variable {K σ : Type} [Field K]

def restrictHyperplaneHom {S T : Subfield K} (h : S ≤ T)
    (f : (MvPolynomial σ T)[X] →ₐ[T] K) : (MvPolynomial σ S)[X] →ₐ[S] K where
  toRingHom := f.toRingHom.comp (Polynomial.mapRingHom (MvPolynomial.map (Subfield.inclusion h)))
  commutes' s := by
    change f (Polynomial.map (MvPolynomial.map (Subfield.inclusion h))
      (C (MvPolynomial.C s))) = (s : K)
    simp only [map_C, MvPolynomial.map_C]
    exact f.commutes (Subfield.inclusion h s)

lemma restrictHyperplaneHom_injective {S T : Subfield K} (h : S ≤ T)
    (f : (MvPolynomial σ T)[X] →ₐ[T] K) (hf : Function.Injective f) :
    Function.Injective (restrictHyperplaneHom h f) :=
  hf.comp (Polynomial.map_injective _ (MvPolynomial.map_injective _ (Subfield.inclusion h).injective))

@[simp] lemma restrictHyperplaneHom_X {S T : Subfield K} (h : S ≤ T)
    (f : (MvPolynomial σ T)[X] →ₐ[T] K) : restrictHyperplaneHom h f X = f X := by
  change f (Polynomial.map _ X) = f X
  rw [Polynomial.map_X]

@[simp] lemma restrictHyperplaneHom_CX {S T : Subfield K} (h : S ≤ T)
    (f : (MvPolynomial σ T)[X] →ₐ[T] K) (i : σ) :
    restrictHyperplaneHom h f (C (MvPolynomial.X i)) = f (C (MvPolynomial.X i)) := by
  change f (Polynomial.map _ (C (MvPolynomial.X i))) = f (C (MvPolynomial.X i))
  simp only [map_C, MvPolynomial.map_X]

theorem common_hyperplane_field {ι : Type} [Countable ι]
    (S : ι → Subfield K) (hS : ∀ i, Countable (S i))
    (c : Set K) (hc : c.Countable) :
    ∃ T : Subfield K, Countable T ∧ c ⊆ T ∧ ∀ i, S i ≤ T := by
  let d : Set K := c ∪ ⋃ i, (S i : Set K)
  have hd : d.Countable := hc.union (Set.countable_iUnion fun i => by
    let := hS i
    exact Set.to_countable _)
  let T := Subfield.closure d
  have hT : Countable T := Cardinal.mk_le_aleph0_iff.mp
    ((Subfield.cardinalMk_closure_le_max _).trans (max_le hd.le_aleph0 le_rfl))
  exact ⟨T, hT, fun _ hx => Subfield.subset_closure (Or.inl hx),
    fun i _ hx => Subfield.subset_closure (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))⟩

theorem simultaneous_generic_hyperplane_parameters {ι : Type} [Countable ι]
    (P : ι → (σ → K) → K → Prop)
    (hP : ∀ i, ∃ S : Subfield K, Countable S ∧
      ∀ f : (MvPolynomial σ S)[X] →ₐ[S] K, Function.Injective f →
        P i (fun k => f (C (MvPolynomial.X k))) (f X))
    (c : Set K) (hc : c.Countable) :
    ∃ T : Subfield K, Countable T ∧ c ⊆ T ∧
      ∀ f : (MvPolynomial σ T)[X] →ₐ[T] K, Function.Injective f →
        ∀ i, P i (fun k => f (C (MvPolynomial.X k))) (f X) := by
  choose S hS hP using hP
  obtain ⟨T, hT, hcT, hST⟩ := common_hyperplane_field S hS c hc
  refine ⟨T, hT, hcT, fun f hf i => ?_⟩
  simpa only [restrictHyperplaneHom_CX, restrictHyperplaneHom_X] using
    hP i (restrictHyperplaneHom (hST i) f) (restrictHyperplaneHom_injective (hST i) f hf)

theorem independent_hyperplane_parameters [Fintype σ] [IsAlgClosed K] [Uncountable K]
    (T : Subfield K) [Countable T] :
    ∃ f : (MvPolynomial σ T)[X] →ₐ[T] K, Function.Injective f := by
  let : Countable (MvPolynomial σ T) := AddMonoidAlgebra.coeff_injective.countable
  let : Countable (AddMonoidAlgebra (MvPolynomial σ T) ℕ) :=
    AddMonoidAlgebra.coeff_injective.countable
  let : Countable (MvPolynomial σ T)[X] := Polynomial.toFinsupp_injective.countable
  have hcard : Cardinal.mk (FractionRing (MvPolynomial σ T)[X]) ≤ Cardinal.mk K := by
    rw [Cardinal.mk_fractionRing]
    exact Cardinal.mk_le_aleph0.trans (le_of_lt Cardinal.aleph0_lt_mk)
  obtain ⟨g⟩ := field_embedding_over_countable (R := T) hcard
  refine ⟨g.comp (IsScalarTower.toAlgHom T (MvPolynomial σ T)[X]
    (FractionRing (MvPolynomial σ T)[X])), ?_⟩
  change Function.Injective (fun x : (MvPolynomial σ T)[X] =>
    g (algebraMap (MvPolynomial σ T)[X] (FractionRing (MvPolynomial σ T)[X]) x))
  exact g.injective.comp (IsFractionRing.injective (MvPolynomial σ T)[X] (FractionRing (MvPolynomial σ T)[X]))

end

noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem simultaneous_etale_integral_hyperplanes
    {K ι : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable ι] (A σ : ι → Type) [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)]
    [∀ j, Algebra K (A j)] [∀ j, Algebra.FiniteType K (A j)]
    [∀ j, Algebra (MvPolynomial (σ j) K) (A j)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) (A j)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) (A j)]
    (v : ∀ j, Fin n → A j) (i₁ i₂ : ι → Fin n) (a b : ∀ j, σ j)
    (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, v j (i₁ j) = algebraMap (MvPolynomial (σ j) K) (A j) (MvPolynomial.X (a j)))
    (hvb : ∀ j, v j (i₂ j) = algebraMap (MvPolynomial (σ j) K) (A j) (MvPolynomial.X (b j)))
    (c : Set K) (hc : c.Countable) :
    ∃ T : Subfield K, Countable T ∧ c ⊆ T ∧
      ∃ f : (MvPolynomial (Fin n) T)[X] →ₐ[T] K, Function.Injective f ∧
        ∀ j, IsDomain (A j ⧸ Ideal.span {algebraMap K (A j) (f X) -
          ∑ k, algebraMap K (A j) (f (C (MvPolynomial.X k))) * v j k}) := by
  let P (j : ι) (α : Fin n → K) (β : K) : Prop :=
    IsDomain (A j ⧸ Ideal.span {algebraMap K (A j) β - ∑ k, algebraMap K (A j) (α k) * v j k})
  have hP j : ∃ S : Subfield K, Countable S ∧
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
        P j (fun k => f (C (MvPolynomial.X k))) (f X) := by
    obtain ⟨S, hS, _, h⟩ := etale_generic_hyperplane_section
      (v j) (i₁ j) (i₂ j) (a j) (b j) (hab j) (hva j) (hvb j)
      (∅ : Set K) Set.countable_empty
    exact ⟨S, hS, h⟩
  obtain ⟨T, hT, hcT, hh⟩ := simultaneous_generic_hyperplane_parameters P hP c hc
  let : Countable T := hT
  obtain ⟨f, hf⟩ := independent_hyperplane_parameters (σ := Fin n) T
  exact ⟨T, hT, hcT, f, hf, hh f hf⟩

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
