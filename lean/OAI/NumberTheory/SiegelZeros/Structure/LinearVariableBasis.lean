import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.NormalizationPresentationLocalEquiv

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
open Module TensorProduct
namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem finite_normalization_local_finrank_eq_length_mul_rank
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F] [Finite σ]
    [Algebra B F] [IsFractionRing B F]
    (I p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [Module.Finite B (MvPolynomial σ B ⧸ p)]
    (hp : p.comap MvPolynomial.C = ⊥) (hpI : p ∈ I.minimalPrimes) :
    letI := coefficient_localization_isMaximal_of_finite (F := F) p hp
    let q := p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))
    (Module.finrank F
      (Localization.AtPrime q ⧸
        (I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).map
          (algebraMap _ (Localization.AtPrime q))) : ℕ∞) =
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap _ (Localization.AtPrime p))) *
        (Module.finrank B (MvPolynomial σ B ⧸ p) : ℕ∞) := by
  let := coefficient_localization_isMaximal_of_finite (F := F) p hp
  exact coefficient_localization_component_finrank_eq_length_mul_rank I p hp hpI

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.GeometryAcceptance

theorem mem_minimalPrimes_of_local_radical_eq_maximal
    {R : Type*} [CommRing R] (I p : Ideal R) [p.IsPrime]
    (hrad : (I.map (algebraMap R (Localization.AtPrime p))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime p)) : p ∈ I.minimalPrimes := by
  have hlocal : IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
      (I.map (algebraMap R (Localization.AtPrime p))).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  rwa [IsLocalization.minimalPrimes_map p.primeCompl (Localization.AtPrime p) I,
    Set.mem_preimage, Localization.AtPrime.under_maximalIdeal] at hlocal

end WeightedTorusJets.GeometryAcceptance

namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial Module


def linearVariableBasis (K σ : Type*) [Field K] :
    Basis σ K (homogeneousSubmodule σ K 1) :=
  (Basis.span (linearIndependent_X σ K)).map
    (LinearEquiv.ofEq _ _ homogeneousSubmodule_one_eq_span_X.symm)

@[simp] theorem linearVariableBasis_apply {K σ : Type*} [Field K] (i : σ) :
    (linearVariableBasis K σ i : MvPolynomial σ K) = X i := by
  simp [linearVariableBasis]

theorem normalization_linearForms_independent
    {K σ ι : Type*} [Field K] (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : Function.Injective g) (l : ι → homogeneousSubmodule σ K 1)
    (hl : ∀ i, g (X i) = Ideal.Quotient.mk P (l i)) :
    LinearIndependent K l := by
  have hx : AlgebraicIndependent K (fun i => g (X i)) := by
    rw [algebraicIndependent_iff_injective_aeval]
    have he : aeval (fun i => g (X i)) = g := by ext i; simp
    simpa only [he] using hg
  have hcomp : (Ideal.Quotient.mkₐ K P).toLinearMap.comp
      (homogeneousSubmodule σ K 1).subtype ∘ l = (fun i => g (X i)) := by
    funext i
    exact (hl i).symm
  apply LinearIndependent.of_comp ((Ideal.Quotient.mkₐ K P).toLinearMap.comp
    (homogeneousSubmodule σ K 1).subtype)
  rw [hcomp]
  exact hx.linearIndependent

theorem symmetric_basis_coordinate_mem_degree_one
    {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    (b : Basis ι K M) (m : M) :
    SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι K M m) ∈
      homogeneousSubmodule ι K 1 := by
  let L := (SymmetricAlgebra.equivMvPolynomial b).toLinearMap.comp (SymmetricAlgebra.ι K M)
  have hs : Submodule.span K (Set.range b) ≤ (homogeneousSubmodule ι K 1).comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι K M (b i)) ∈
      homogeneousSubmodule ι K 1
    simpa using (isHomogeneous_X K i)
  apply hs
  rw [b.span_eq]
  exact Submodule.mem_top

theorem symmetric_standard_coordinates
    {K σ : Type*} [Field K] (l : homogeneousSubmodule σ K 1) :
    SymmetricAlgebra.equivMvPolynomial (linearVariableBasis K σ)
      (SymmetricAlgebra.ι K (homogeneousSubmodule σ K 1) l) = (l : MvPolynomial σ K) := by
  have he : (SymmetricAlgebra.equivMvPolynomial (linearVariableBasis K σ)).toLinearMap.comp
      (SymmetricAlgebra.ι K (homogeneousSubmodule σ K 1)) =
      (homogeneousSubmodule σ K 1).subtype := by
    apply (linearVariableBasis K σ).ext
    intro i
    simp
  exact congrArg (fun f : homogeneousSubmodule σ K 1 →ₗ[K] MvPolynomial σ K => f l) he

def polynomialCoordinatesOfLinearBasis
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1)) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial σ K :=
  (SymmetricAlgebra.equivMvPolynomial b).symm.trans
    (SymmetricAlgebra.equivMvPolynomial (linearVariableBasis K σ))

@[simp] theorem polynomialCoordinatesOfLinearBasis_X
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1)) (i : ι) :
    polynomialCoordinatesOfLinearBasis b (X i) = (b i : MvPolynomial σ K) := by
  simp [polynomialCoordinatesOfLinearBasis, symmetric_standard_coordinates]

theorem polynomialCoordinatesOfLinearBasis_symm_X_homogeneous
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1)) (j : σ) :
    ((polynomialCoordinatesOfLinearBasis b).symm (X j)).IsHomogeneous 1 := by
  change ((SymmetricAlgebra.equivMvPolynomial b)
    ((SymmetricAlgebra.equivMvPolynomial (linearVariableBasis K σ)).symm (X j))).IsHomogeneous 1
  rw [SymmetricAlgebra.equivMvPolynomial_symm_X]
  exact symmetric_basis_coordinate_mem_degree_one b _

theorem polynomialCoordinatesOfLinearBasis_homogeneous
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1))
    {p : MvPolynomial ι K} {d : ℕ} (hp : p.IsHomogeneous d) :
    (polynomialCoordinatesOfLinearBasis b p).IsHomogeneous d := by
  have he : aeval (fun i => polynomialCoordinatesOfLinearBasis b (X i)) =
      (polynomialCoordinatesOfLinearBasis b).toAlgHom := by ext i; simp
  simpa only [one_mul, he, AlgEquiv.coe_toAlgHom] using hp.aeval (n := 1)
    (fun i => polynomialCoordinatesOfLinearBasis b (X i))
    (fun i => by rw [polynomialCoordinatesOfLinearBasis_X]; exact (b i).property)

theorem polynomialCoordinatesOfLinearBasis_symm_homogeneous
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1))
    {p : MvPolynomial σ K} {d : ℕ} (hp : p.IsHomogeneous d) :
    ((polynomialCoordinatesOfLinearBasis b).symm p).IsHomogeneous d := by
  have he : aeval (fun i => (polynomialCoordinatesOfLinearBasis b).symm (X i)) =
      (polynomialCoordinatesOfLinearBasis b).symm.toAlgHom := by ext i; simp
  simpa only [one_mul, he, AlgEquiv.coe_toAlgHom] using hp.aeval (n := 1)
    (fun i => (polynomialCoordinatesOfLinearBasis b).symm (X i))
    (polynomialCoordinatesOfLinearBasis_symm_X_homogeneous b)

theorem basis_sumExtend_inl {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    {v : ι → M} (hv : LinearIndependent K v) (i : ι) :
    Basis.sumExtend hv (Sum.inl i) = v i := by
  simp only [Basis.sumExtend, Basis.reindex_apply, Basis.coe_extend]
  rfl

theorem exists_linearBasis_extension
    {K σ ι : Type*} [Field K] [Finite σ] [Finite ι]
    {l : ι → homogeneousSubmodule σ K 1} (hl : LinearIndependent K l) :
    ∃ h : ℕ, Nat.card ι + h = Nat.card σ ∧
      ∃ b : Basis (ι ⊕ Fin h) K (homogeneousSubmodule σ K 1),
        ∀ i, b (Sum.inl i) = l i := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype ι := Fintype.ofFinite ι
  let : Module.Finite K (homogeneousSubmodule σ K 1) := Module.Finite.of_basis (linearVariableBasis K σ)
  let b₀ := Basis.sumExtend hl
  let J := Basis.sumExtendIndex hl
  have : Finite (ι ⊕ J) := Module.Finite.finite_basis b₀
  let : Finite J := Finite.of_injective (Sum.inr : J → ι ⊕ J) Sum.inr_injective
  let : Fintype J := Fintype.ofFinite J
  let e : (ι ⊕ J) ≃ (ι ⊕ Fin (Fintype.card J)) :=
    Equiv.sumCongr (Equiv.refl ι) (Fintype.equivFin J)
  refine ⟨Fintype.card J, ?_, b₀.reindex e, ?_⟩
  · have he := (Module.finrank_eq_card_basis b₀).symm.trans
      (Module.finrank_eq_card_basis (linearVariableBasis K σ))
    simpa only [Fintype.card_sum, Nat.card_eq_fintype_card] using he
  · intro i
    simpa [Basis.reindex_apply, e, b₀] using basis_sumExtend_inl hl i


end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial Module

theorem totalDegree_algHom_le_of_linear_images
    {K σ τ : Type*} [Field K]
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (hf : ∀ i, (f (X i)).totalDegree ≤ 1) (p : MvPolynomial σ K) :
    (f p).totalDegree ≤ p.totalDegree := by
  have h := totalDegree_eval₂_le_of_linear_images (RingHom.id K)
    (fun i => f (X i)) hf p
  have he : eval₂Hom (C.comp (RingHom.id K)) (fun i => f (X i)) = f.toRingHom := by
    ext i <;> simp
  change ((eval₂Hom (C.comp (RingHom.id K)) (fun i => f (X i))) p).totalDegree ≤ _ at h
  rw [he] at h
  exact h

theorem polynomialCoordinatesOfLinearBasis_totalDegree
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1))
    (p : MvPolynomial ι K) :
    (polynomialCoordinatesOfLinearBasis b p).totalDegree = p.totalDegree := by
  let e := polynomialCoordinatesOfLinearBasis b
  have hf : ∀ i, (e (X i)).totalDegree ≤ 1 := by
    intro i
    change (polynomialCoordinatesOfLinearBasis b (X i)).totalDegree ≤ 1
    rw [polynomialCoordinatesOfLinearBasis_X]
    exact IsHomogeneous.totalDegree_le (b i).property
  have hb : ∀ i, (e.symm (X i)).totalDegree ≤ 1 := fun i =>
    (polynomialCoordinatesOfLinearBasis_symm_X_homogeneous b i).totalDegree_le
  apply le_antisymm (totalDegree_algHom_le_of_linear_images e.toAlgHom hf p)
  simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
    totalDegree_algHom_le_of_linear_images e.symm.toAlgHom hb (e p)

theorem polynomialCoordinatesOfLinearBasis_symm_totalDegree
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1))
    (p : MvPolynomial σ K) :
    ((polynomialCoordinatesOfLinearBasis b).symm p).totalDegree = p.totalDegree := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (polynomialCoordinatesOfLinearBasis_totalDegree b
      ((polynomialCoordinatesOfLinearBasis b).symm p)).symm

theorem exists_normalization_linear_coordinates
    {K σ ι : Type*} [Field K] [Finite σ] [Finite ι]
    (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : Function.Injective g)
    (hl : ∀ i, ∃ l : MvPolynomial σ K, l.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk P l) :
    ∃ h : ℕ, Nat.card ι + h = Nat.card σ ∧
      ∃ e : MvPolynomial (ι ⊕ Fin h) K ≃ₐ[K] MvPolynomial σ K,
        (∀ i, g (X i) = Ideal.Quotient.mk P (e (X (Sum.inl i)))) ∧
        (∀ p, (e p).totalDegree = p.totalDegree) ∧
        (∀ p, (e.symm p).totalDegree = p.totalDegree) ∧
        (∀ p d, p.IsHomogeneous d → (e p).IsHomogeneous d) ∧
        (∀ p d, p.IsHomogeneous d → (e.symm p).IsHomogeneous d) := by
  classical
  choose l hlh hlg using hl
  let l' : ι → homogeneousSubmodule σ K 1 := fun i => ⟨l i, hlh i⟩
  have hli := normalization_linearForms_independent P g hg l' hlg
  obtain ⟨h, hc, b, hb⟩ := exists_linearBasis_extension hli
  refine ⟨h, hc, polynomialCoordinatesOfLinearBasis b, ?_,
    polynomialCoordinatesOfLinearBasis_totalDegree b,
    polynomialCoordinatesOfLinearBasis_symm_totalDegree b, ?_, ?_⟩
  · intro i
    rw [polynomialCoordinatesOfLinearBasis_X, hb]
    exact hlg i
  · intro p d hp
    exact polynomialCoordinatesOfLinearBasis_homogeneous b hp
  · intro p d hp
    exact polynomialCoordinatesOfLinearBasis_symm_homogeneous b hp

theorem exists_normalization_linear_coordinates_of_count
    {K σ : Type*} [Field K] [Finite σ] {s h : ℕ}
    (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : Function.Injective g)
    (hl : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk P l)
    (hc : s + h = Nat.card σ) :
    ∃ e : MvPolynomial (Fin s ⊕ Fin h) K ≃ₐ[K] MvPolynomial σ K,
      (∀ i, g (X i) = Ideal.Quotient.mk P (e (X (Sum.inl i)))) ∧
      (∀ p, (e p).totalDegree = p.totalDegree) ∧
      (∀ p, (e.symm p).totalDegree = p.totalDegree) ∧
      (∀ p d, p.IsHomogeneous d → (e p).IsHomogeneous d) ∧
      (∀ p d, p.IsHomogeneous d → (e.symm p).IsHomogeneous d) := by
  obtain ⟨h', hc', e, he⟩ := exists_normalization_linear_coordinates P g hg hl
  have hh : h' = h := by
    apply Nat.add_left_cancel (n := s)
    simpa only [Nat.card_fin, hc] using hc'
  subst h'
  exact ⟨e, he⟩

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem quotient_length_congr_ideal
    {R : Type*} [CommRing R] (I J : Ideal R) (h : I = J) :
    Module.length R (R ⧸ I) = Module.length R (R ⧸ J) := by
  subst J
  rfl

theorem quotient_finrank_congr_ideal
    {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (I J : Ideal R) (h : I = J) :
    Module.finrank K (R ⧸ I) = Module.finrank K (R ⧸ J) := by
  subst J
  rfl

theorem coefficient_localization_weighted_length_le_pow
    {B F : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (h D : ℕ) (p : Ideal (MvPolynomial (Fin h) B)) [p.IsPrime]
    [Module.Finite B (MvPolynomial (Fin h) B ⧸ p)]
    (hp : p.comap MvPolynomial.C = ⊥)
    (f : Fin h → MvPolynomial (Fin h) B)
    (hf : ∀ i, (MvPolynomial.map (algebraMap B F) (f i)).totalDegree ≤ D)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap _ (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ Ideal.span (Set.range (fun i =>
        algebraMap _ (Localization.AtPrime p) (f i)))) *
      (Module.finrank B (MvPolynomial (Fin h) B ⧸ p) : ℕ∞) ≤ (D ^ h : ℕ) := by
  let I := Ideal.span (Set.range f)
  have hm : p ∈ I.minimalPrimes :=
    GeometryAcceptance.mem_minimalPrimes_of_local_radical_eq_maximal I p
      (by simpa only [I, Ideal.map_span, ← Set.range_comp, Function.comp_def] using hrad)
  have hn := coefficient_localization_finrank_le_pow (F := F) h D p hp f hf hrad
  have he := finite_normalization_local_finrank_eq_length_mul_rank (F := F) I p hp hm
  let := coefficient_localization_isMaximal_of_finite (F := F) p hp
  let q := p.map (algebraMap (MvPolynomial (Fin h) B) (MvPolynomial (Fin h) F))
  let J := Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime p) (f i)))
  let JF := Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime q)
    (MvPolynomial.map (algebraMap B F) (f i))))
  have hI : I.map (algebraMap _ (Localization.AtPrime p)) = J := by
    dsimp only [I]
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hIF : (I.map (algebraMap (MvPolynomial (Fin h) B)
      (MvPolynomial (Fin h) F))).map (algebraMap _ (Localization.AtPrime q)) = JF := by
    dsimp only [I]
    rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
    rfl
  have hlength := quotient_length_congr_ideal _ _ hI
  have hdimension := quotient_finrank_congr_ideal (K := F) _ _ hIF
  calc
    _ = Module.length (Localization.AtPrime p)
          (Localization.AtPrime p ⧸ I.map (algebraMap _ (Localization.AtPrime p))) *
          (Module.finrank B (MvPolynomial (Fin h) B ⧸ p) : ℕ∞) := by rw [hlength]
    _ = (Module.finrank F (Localization.AtPrime q ⧸
          (I.map (algebraMap (MvPolynomial (Fin h) B) (MvPolynomial (Fin h) F))).map
            (algebraMap _ (Localization.AtPrime q))) : ℕ∞) := he.symm
    _ = (Module.finrank F (Localization.AtPrime q ⧸ JF) : ℕ∞) := by rw [hdimension]
    _ ≤ (D ^ h : ℕ) := by exact_mod_cast hn

theorem linear_normalization_weighted_local_length_le
    {K σ : Type*} [Field K] [Finite σ] {s h D : ℕ}
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : Function.Injective g)
    (hfinite : letI := g.toAlgebra
      letI : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
      Module.Finite (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P))
    (hlin : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (MvPolynomial.X i) = Ideal.Quotient.mk P l)
    (hcount : s + h = Nat.card σ)
    (f : Fin h → MvPolynomial σ K)
    (hf : ∀ i, (f i).totalDegree ≤ D)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    letI := g.toAlgebra
    letI : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ Ideal.span (Set.range (fun i =>
        algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (f i)))) *
      (Module.finrank (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) : ℕ∞) ≤
        (D ^ h : ℕ) := by
  let := g.toAlgebra
  let : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
  obtain ⟨e, he, _, heinv, _, _⟩ :=
    exists_normalization_linear_coordinates_of_count P g hg hlin hcount
  let p := P.comap (normalizationPresentation e).symm.toRingHom
  let : p.IsPrime := Ideal.IsPrime.comap _
  have hp : p.comap MvPolynomial.C = ⊥ :=
    normalizationPresentation_coefficient_comap_eq_bot e P g hg he
  let : Module.Finite (MvPolynomial (Fin s) K)
      (MvPolynomial (Fin h) (MvPolynomial (Fin s) K) ⧸ p) :=
    finite_normalizationPresentation_quotient e P g he hfinite
  have hdeg (i : Fin h) :
      (MvPolynomial.map (algebraMap (MvPolynomial (Fin s) K)
          (FractionRing (MvPolynomial (Fin s) K)))
        (normalizationPresentation e (f i))).totalDegree ≤ D :=
    (totalDegree_localized_normalizationPresentation_le e (f i)).trans
      ((heinv (f i)).le.trans (hf i))
  have hrad' := normalizationPresentation_radical_eq_maximal e P f hrad
  have hn := coefficient_localization_weighted_length_le_pow
    (F := FractionRing (MvPolynomial (Fin s) K)) h D p hp
    (fun i => normalizationPresentation e (f i)) hdeg hrad'
  have hlength := quotient_length_eq_of_commuting_images
    (normalizationPresentationLocalEquiv e P).toRingEquiv
    (fun i => algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (f i))
    (fun i => algebraMap _ (Localization.AtPrime p) (normalizationPresentation e (f i)))
    (fun i => normalizationPresentationLocalEquiv_algebraMap e P (f i))
  have hrank := (normalizationPresentationQuotientEquiv e P g he).toLinearEquiv.finrank_eq
  rw [hlength, ← hrank]
  exact hn

end WeightedTorusJets.Geometry.DegreeBezout

end


end SiegelZeros

end OAI
