import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.DifferentialFrames

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.LinearBertini
noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.Bertini MaximalSeshadri.FrameBertini
variable {K L A ι : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]

theorem parameters_dependent [Algebra.EssFiniteType K L] [Fintype ι]
    (v a : ι → L) (hunit : Ideal.span (Set.range v) = ⊤)
    (hzero : ∑ i, a i * v i = 0)
    (hcritical : ∑ i, a i • D K L (v i) = 0) :
    ¬ AlgebraicIndependent K a := by
  intro ha
  have hd := congrArg (D K L) hzero
  simp only [map_sum, Derivation.leibniz, map_zero, Finset.sum_add_distrib,
    hcritical, zero_add] at hd
  have hi := algebraicIndependent_differentials a ha
  have hz := (Fintype.linearIndependent_iff.mp hi) v hd
  have hbot : Ideal.span (Set.range v) ≤ ⊥ := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hz i
  rw [hunit] at hbot
  exact top_ne_bot (le_antisymm hbot bot_le)

 theorem parameters_polynomial [Algebra.EssFiniteType K L] [Fintype ι]
    (v a : ι → L) (hunit : Ideal.span (Set.range v) = ⊤)
    (hzero : ∑ i, a i * v i = 0)
    (hcritical : ∑ i, a i • D K L (v i) = 0) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ MvPolynomial.aeval a p = 0 := by
  have h := parameters_dependent v a hunit hzero hcritical
  classical
  rw [algebraicIndependent_iff] at h
  push Not at h
  obtain ⟨p, hp, hne⟩ := h
  exact ⟨p, hne, hp⟩

variable [CommRing A] [Algebra K A]

lemma parameters_polynomial_image [Algebra.EssFiniteType K L] [Fintype ι]
    [Algebra A L] [IsScalarTower K A L]
    (v a : ι → A) (hunit : Ideal.span (Set.range v) = ⊤)
    (hzero : ∑ i, a i * v i = 0)
    (hcritical : ∑ i, a i • D K A (v i) = 0) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      MvPolynomial.aeval (fun i => algebraMap A L (a i)) p = 0 := by
  apply parameters_polynomial (fun i => algebraMap A L (v i))
  · have h := congrArg (Ideal.map (algebraMap A L)) hunit
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, Ideal.map_top] using h
  · simpa only [map_sum, map_mul, map_zero] using congrArg (algebraMap A L) hzero
  · have h := congrArg (KaehlerDifferential.map K K A L) hcritical
    simp only [IsScalarTower.algebraMap_smul]
    simpa only [map_sum, map_smul, KaehlerDifferential.map_D, map_zero] using h

theorem incidence_polynomial [Algebra.FiniteType K A] [Fintype ι]
    (v a : ι → A) (hunit : Ideal.span (Set.range v) = ⊤)
    (hzero : ∑ i, a i * v i = 0)
    (hcritical : ∑ i, a i • D K A (v i) = 0) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ IsNilpotent (MvPolynomial.aeval a p) := by
  classical
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let Q := minimalPrimes A
  let : Fintype Q := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  have hf : ∀ q : Q, ∃ p : MvPolynomial ι K,
      p ≠ 0 ∧ MvPolynomial.aeval a p ∈ q.val := by
    intro q
    let : q.val.IsPrime := q.property.isPrime
    let B := A ⧸ q.val
    let F := FractionRing B
    let : Algebra.EssFiniteType B F :=
      Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors B)
    let : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K B F
    obtain ⟨p, hp, he⟩ := parameters_polynomial_image (L := F) v a hunit hzero hcritical
    refine ⟨p, hp, ?_⟩
    have he' : algebraMap A F (MvPolynomial.aeval a p) = 0 := by
      change (IsScalarTower.toAlgHom K A F) (MvPolynomial.aeval a p) = 0
      rw [MvPolynomial.comp_aeval_apply a (IsScalarTower.toAlgHom K A F)]
      exact he
    have hinj : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
    rw [IsScalarTower.algebraMap_apply A B F] at he'
    have hq : algebraMap A B (MvPolynomial.aeval a p) = 0 :=
      hinj (he'.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  choose p hp hm using hf
  refine ⟨∏ q : Q, p q, Finset.prod_ne_zero_iff.mpr (fun q _ => hp q), ?_⟩
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  let : J.IsPrime := hJ
  obtain ⟨q, hq, hqJ⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := J) bot_le
  simp only [map_prod]
  apply (Ideal.IsPrime.prod_mem_iff).mpr
  exact ⟨⟨q, hq⟩, Finset.mem_univ _, hqJ (hm ⟨q, hq⟩)⟩

end
noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.Bertini MaximalSeshadri.FrameBertini
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

def universalSection (v : ι → R) : MvPolynomial ι R :=
  ∑ i, X i * C (v i)

def universalGradient (b : DifferentialFrame K R κ) (v : ι → R)
    (j : κ) : MvPolynomial ι R :=
  ∑ i, X i * C (b.coord (D K R (v i)) j)

def criticalIdeal (b : DifferentialFrame K R κ) (v : ι → R) :
    Ideal (MvPolynomial ι R) :=
  Ideal.span (insert (universalSection v) (Set.range (universalGradient b v)))

theorem universal_critical_polynomial [Algebra.FiniteType K R]
    (b : DifferentialFrame K R κ) (v : ι → R)
    (hunit : Ideal.span (Set.range v) = ⊤) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      IsNilpotent (MvPolynomial.aeval (fun i =>
        algebraMap (MvPolynomial ι R)
          (MvPolynomial ι R ⧸ criticalIdeal b v) (X i)) p) := by
  let T := MvPolynomial ι R
  let A := T ⧸ criticalIdeal b v
  let a : ι → A := fun i => algebraMap T A (X i)
  have hC (r : R) : algebraMap T A (C r) = algebraMap R A r := rfl
  have hzero : ∑ i, a i * algebraMap R A (v i) = 0 := by
    have he : algebraMap T A (universalSection v) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
    simpa only [universalSection, map_add, map_sum, map_mul,
      hC, a] using he
  have hgrad : ∀ j, ∑ i, a i *
      algebraMap R A (b.coord (D K R (v i)) j) = 0 := by
    intro j
    have he : algebraMap T A (universalGradient b v j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j)))
    simpa only [universalGradient, map_sum, map_mul,
      hC, a] using he
  have hunit' : Ideal.span (Set.range (fun i => algebraMap R A (v i))) = ⊤ := by
    have h := congrArg (Ideal.map (algebraMap R A)) hunit
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, Ideal.map_top] using h
  exact incidence_polynomial (fun i => algebraMap R A (v i)) a hunit' hzero
    (critical_of_coordinates b v a hgrad)

end

noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.Bertini MaximalSeshadri.FrameBertini
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

def specializedSection (v : ι → R) (t : ι → K) : R :=
  ∑ i, algebraMap K R (t i) * v i

def specializedGradient (b : DifferentialFrame K R κ) (v : ι → R)
    (t : ι → K) (j : κ) : R :=
  ∑ i, algebraMap K R (t i) * b.coord (D K R (v i)) j

omit [CharZero K] in

theorem critical_specialization_eq_top
    (b : DifferentialFrame K R κ) (v : ι → R) (p : MvPolynomial ι K)
    (hp : IsNilpotent (MvPolynomial.aeval (fun i =>
        algebraMap (MvPolynomial ι R)
          (MvPolynomial ι R ⧸ criticalIdeal b v) (X i)) p))
    (t : ι → K) (ht : MvPolynomial.aeval t p ≠ 0) :
    Ideal.span (insert (specializedSection v t)
      (Set.range (specializedGradient b v t))) = ⊤ := by
  classical
  by_contra hne
  let J := Ideal.span (insert (specializedSection v t)
    (Set.range (specializedGradient b v t)))
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
  let : M.IsMaximal := hM
  let B := R ⧸ M
  let T := MvPolynomial ι R
  let A := T ⧸ criticalIdeal b v
  let φ : T →ₐ[K] B := (MvPolynomial.aeval (fun i => algebraMap K B (t i))).restrictScalars K
  have hφX (i : ι) : φ (X i) = algebraMap K B (t i) := MvPolynomial.aeval_X _ _
  have hφC (r : R) : φ (C r) = algebraMap R B r := MvPolynomial.aeval_C _ _
  have hφs : φ (universalSection v) = 0 := by
    have he : algebraMap R B (specializedSection v t) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hJM (Ideal.subset_span (Set.mem_insert _ _)))
    simpa only [universalSection, specializedSection, map_add, map_sum, map_mul, hφX, hφC,
      IsScalarTower.algebraMap_apply K R B] using he
  have hφg (j : κ) : φ (universalGradient b v j) = 0 := by
    have he : algebraMap R B (specializedGradient b v t j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (hJM (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j))))
    simpa only [universalGradient, specializedGradient, map_sum, map_mul, hφX, hφC,
      IsScalarTower.algebraMap_apply K R B] using he
  have hker : criticalIdeal b v ≤ RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro x (rfl | ⟨j, rfl⟩)
    · exact hφs
    · exact hφg j
  let ψ : A →ₐ[K] B := Ideal.Quotient.liftₐ (criticalIdeal b v) φ (fun x hx => hker hx)
  have hspec : IsNilpotent (algebraMap K B (MvPolynomial.aeval t p)) := by
    have h := hp.map ψ
    have hψ (i : ι) : ψ (algebraMap T A (X i)) = algebraMap K B (t i) := by
      change φ (X i) = algebraMap K B (t i)
      exact hφX i
    rw [MvPolynomial.comp_aeval_apply, show (fun i =>
      ψ (algebraMap T A (X i))) = (fun i => algebraMap K B (t i)) from funext hψ] at h
    have he := MvPolynomial.comp_aeval_apply t (Algebra.ofId K B) p
    exact he ▸ h
  exact hspec.not_isUnit ((isUnit_iff_ne_zero.mpr ht).map (algebraMap K B))

end

noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.Bertini MaximalSeshadri.FrameBertini
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

omit [CharZero K] in
lemma specializedGradient_eq (b : DifferentialFrame K R κ) (v : ι → R)
    (t : ι → K) (j : κ) :
    b.coord (D K R (specializedSection v t)) j = specializedGradient b v t j := by
  simp only [specializedSection, specializedGradient, map_sum,
    Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
    Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]

theorem affine_bertini_smooth [Algebra.Smooth K R]
    (b : DifferentialFrame K R κ) (v : ι → R)
    (hunit : Ideal.span (Set.range v) = ⊤) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        Algebra.Smooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) := by
  obtain ⟨p, hp, hcrit⟩ := universal_critical_polynomial b v hunit
  refine ⟨p, hp, fun t ht => ?_⟩
  have hgrad := critical_specialization_eq_top b v p hcrit t ht
  rw [show specializedGradient b v t = (fun j =>
    b.coord (D K R (specializedSection v t)) j) from
      funext (fun j => (specializedGradient_eq b v t j).symm)] at hgrad
  let : Algebra.FormallySmooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) :=
    formallySmooth_quotient_of_gradient b (specializedSection v t) hgrad
  let : Algebra.FinitePresentation K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

end

noncomputable section
open MvPolynomial
open MaximalSeshadri.FrameBertini

theorem affine_bertini {K R ι : Type*} [Field K] [CharZero K] [CommRing R]
    [Algebra K R] [Fintype ι] [Algebra.Smooth K R] (v : ι → R)
    (hunit : Ideal.span (Set.range v) = ⊤) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        Algebra.Smooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) := by
  obtain ⟨n, ⟨b⟩⟩ := exists_differentialFrame K R
  exact affine_bertini_smooth b v hunit

theorem simultaneous_affine_bertini {K ι α : Type*} [Field K] [CharZero K]
    [Fintype ι] [Fintype α] (R : α → Type*) [∀ j, CommRing (R j)]
    [∀ j, Algebra K (R j)] [∀ j, Algebra.Smooth K (R j)]
    (v : ∀ j, ι → R j) (hunit : ∀ j, Ideal.span (Set.range (v j)) = ⊤)
    (q : MvPolynomial ι K) (hq : q ≠ 0) :
    ∃ t : ι → K, MvPolynomial.aeval t q ≠ 0 ∧ ∀ j,
      Algebra.Smooth K (R j ⧸ Ideal.span ({specializedSection (v j) t} : Set (R j))) := by
  classical
  choose p hp he using fun j => affine_bertini (K := K) (v j) (hunit j)
  have hprod : q * ∏ j, p j ≠ 0 :=
    mul_ne_zero hq (Finset.prod_ne_zero_iff.mpr (fun j _ => hp j))
  have hex : ∃ t : ι → K, MvPolynomial.aeval t (q * ∏ j, p j) ≠ 0 := by
    by_contra! hn
    apply hprod
    apply MvPolynomial.funext
    intro t
    simpa only [MvPolynomial.aeval_eq_eval, map_zero] using hn t
  obtain ⟨t, ht⟩ := hex
  simp only [map_mul, map_prod, mul_ne_zero_iff] at ht
  refine ⟨t, ht.1, fun j => he j t ?_⟩
  exact Finset.prod_ne_zero_iff.mp ht.2 j (Finset.mem_univ j)
end
end MaximalSeshadri.LinearBertini

namespace MaximalSeshadri.SchemeBertini
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.LinearBertini

theorem smooth_subscheme_of_affine_quotients
    {K α : Type} [Field K] (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K))
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, Algebra K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g) (I : X.IdealSheafData)
    [∀ j, Algebra.Smooth K (Γ(X, (U j).1) ⧸ I.ideal (U j))] :
    Smooth (I.subschemeι ≫ g) := by
  have hOpen (j : α) : IsOpenImmersion (I.subschemeCover.f (U j)) :=
    I.subschemeCover.map_prop (U j)
  let C : I.subscheme.OpenCover := .mkOfCovers α
    (fun j => Spec (CommRingCat.of (Γ(X, (U j).1) ⧸ I.ideal (U j))))
    (fun j => I.subschemeCover.f (U j)) (by
      intro x
      obtain ⟨j, hj⟩ := hcover (I.subschemeι x)
      have hh : x ∈ (I.subschemeCover.f (U j)).opensRange := by
        rw [I.opensRange_subschemeCover_map]
        exact hj
      obtain ⟨y, hy⟩ := hh
      exact ⟨j, y, hy⟩) (by intro j; exact hOpen j)
  let : IsZariskiLocalAtSource (@Smooth.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth.{0}) C
  change ∀ j : α, Smooth (I.subschemeCover.f (U j) ≫ (I.subschemeι ≫ g))
  intro j
  rw [← Category.assoc, I.subschemeCover_map_subschemeι]
  change Smooth (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal (U j))))) ≫
    (U j).2.isoSpec.inv) ≫ (U j).1.ι ≫ g)
  rw [Category.assoc]
  have hu : (U j).2.isoSpec.inv ≫ (U j).1.ι ≫ g = (U j).2.fromSpec ≫ g :=
    (U j).2.isoSpec_inv_ι_assoc g
  rw [hu, ← hOver]
  rw [← Spec.map_comp]
  apply (HasRingHomProperty.Spec_iff (P := @Smooth.{0})).mpr
  change RingHom.Smooth ((Ideal.Quotient.mk (I.ideal (U j))).comp
    (algebraMap K Γ(X, (U j).1)))
  exact RingHom.smooth_algebraMap.mpr inferInstance

theorem smooth_linear_family
    {K α ι : Type} [Field K] [CharZero K] [Fintype α] [Fintype ι]
    (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g]
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, Algebra K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g)
    (v : ∀ j, ι → Γ(X, (U j).1))
    (hunit : ∀ j, Ideal.span (Set.range (v j)) = ⊤)
    (I : (ι → K) → X.IdealSheafData)
    (hI : ∀ t j, (I t).ideal (U j) =
      Ideal.span ({specializedSection (v j) t} : Set Γ(X, (U j).1)))
    (q : MvPolynomial ι K) (hq : q ≠ 0) :
    ∃ t : ι → K, MvPolynomial.aeval t q ≠ 0 ∧ Smooth ((I t).subschemeι ≫ g) := by
  have hS (j : α) : Algebra.Smooth K Γ(X, (U j).1) := by
    apply RingHom.smooth_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @Smooth.{0})
      (φ := CommRingCat.ofHom (algebraMap K Γ(X, (U j).1)))).mp
    rw [hOver]
    have : IsOpenImmersion (U j).2.fromSpec := (U j).2.isOpenImmersion_fromSpec
    exact HasRingHomProperty.comp_of_isOpenImmersion (P := @Smooth.{0})
      (U j).2.fromSpec g inferInstance
  let : ∀ j, Algebra.Smooth K Γ(X, (U j).1) := hS
  obtain ⟨t, ht, hs⟩ := simultaneous_affine_bertini
    (fun j => Γ(X, (U j).1)) v hunit q hq
  refine ⟨t, ht, ?_⟩
  have hQ (j : α) : Algebra.Smooth K (Γ(X, (U j).1) ⧸ (I t).ideal (U j)) := by
    rw [hI]
    exact hs j
  let : ∀ j, Algebra.Smooth K (Γ(X, (U j).1) ⧸ (I t).ideal (U j)) := hQ
  exact smooth_subscheme_of_affine_quotients X g U hcover hOver (I t)
end
end MaximalSeshadri.SchemeBertini


end
end

end OAI
