import Mathlib

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.Bertini
noncomputable section
open scoped TensorProduct
open KaehlerDifferential

lemma mapBaseChange_injective_formallySmooth
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] :
    Function.Injective (KaehlerDifferential.mapBaseChange R A B) := by
  apply (KaehlerDifferential.mapBaseChange R A B).ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
  rw [show y = 0 from Subsingleton.elim _ _, map_zero] at hy
  exact hy.symm ▸ Submodule.zero_mem _

variable {K L ι : Type*} [Field K] [Field L] [CharZero K] [Algebra K L]

theorem algebraicIndependent_differentials [Algebra.EssFiniteType K L]
    (v : ι → L) (hv : AlgebraicIndependent K v) :
    LinearIndependent L (fun i => KaehlerDifferential.D K L (v i)) := by
  let A := MvPolynomial ι K
  let F := FractionRing A
  let a : A →ₐ[K] L := MvPolynomial.aeval v
  let b : F →ₐ[K] L := IsFractionRing.liftAlgHom hv
  let : Algebra A L := a.toRingHom.toAlgebra
  let : Algebra F L := b.toRingHom.toAlgebra
  let : IsScalarTower K A L := IsScalarTower.of_algHom a
  let : IsScalarTower K F L := IsScalarTower.of_algHom b
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun x => by
    change a x = IsFractionRing.lift hv (algebraMap A F x)
    exact (IsFractionRing.lift_algebraMap hv x).symm
  let : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp K F L
  let : Algebra.FormallySmooth A F :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors A)
  let : Algebra.FormallySmooth A L := Algebra.FormallySmooth.comp A F L
  have hinj := mapBaseChange_injective_formallySmooth K A L
  have h := ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange L).linearIndependent
  have h' := h.map' (KaehlerDifferential.mapBaseChange K A L)
    (LinearMap.ker_eq_bot.mpr hinj)
  convert h' using 1
  funext i
  simp only [Function.comp_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  change (D K L) (v i) = (mapBaseChange K A L) (1 ⊗ₜ[A] (D K A) (MvPolynomial.X i))
  rw [mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  congr 1
  exact (MvPolynomial.aeval_X v i).symm

theorem universal_hyperplane_parameters_dependent [Algebra.EssFiniteType K L]
    [Fintype ι] (v : ι → L) (a : Option ι → L)
    (hzero : a none + ∑ i, a (some i) * v i = 0)
    (hcritical : ∑ i, a (some i) • D K L (v i) = 0) :
    ¬ AlgebraicIndependent K a := by
  classical
  intro ha
  have hd := congrArg (D K L) hzero
  simp only [map_add, map_sum, Derivation.leibniz, map_zero, Finset.sum_add_distrib,
    hcritical, zero_add] at hd
  have hs : ∑ j : Option ι, (j.elim 1 v) • D K L (a j) = 0 := by
    simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some, one_smul] using hd
  have hi := algebraicIndependent_differentials a ha
  have he := (Fintype.linearIndependent_iff.mp hi) (fun j : Option ι => j.elim 1 v) hs none
  exact one_ne_zero he

theorem critical_parameters_polynomial [Algebra.EssFiniteType K L]
    [Fintype ι] (v : ι → L) (a : Option ι → L)
    (hzero : a none + ∑ i, a (some i) * v i = 0)
    (hcritical : ∑ i, a (some i) • D K L (v i) = 0) :
    ∃ p : MvPolynomial (Option ι) K, p ≠ 0 ∧ MvPolynomial.aeval a p = 0 := by
  have h := universal_hyperplane_parameters_dependent v a hzero hcritical
  classical
  rw [algebraicIndependent_iff] at h
  push Not at h
  obtain ⟨p, hp, hne⟩ := h
  exact ⟨p, hne, hp⟩

variable {A : Type*} [CommRing A] [Algebra K A]

lemma critical_parameters_polynomial_image [Algebra.EssFiniteType K L]
    [Fintype ι] [Algebra A L] [IsScalarTower K A L]
    (v : ι → A) (a : Option ι → A)
    (hzero : a none + ∑ i, a (some i) * v i = 0)
    (hcritical : ∑ i, a (some i) • D K A (v i) = 0) :
    ∃ p : MvPolynomial (Option ι) K, p ≠ 0 ∧
      MvPolynomial.aeval (fun i => algebraMap A L (a i)) p = 0 := by
  apply critical_parameters_polynomial (fun i => algebraMap A L (v i))
  · simpa only [map_add, map_sum, map_mul, map_zero] using
      congrArg (algebraMap A L) hzero
  · have h := congrArg (KaehlerDifferential.map K K A L) hcritical
    simp only [IsScalarTower.algebraMap_smul]
    simpa only [map_sum, map_smul, KaehlerDifferential.map_D, map_zero] using h

end
end MaximalSeshadri.Bertini
namespace MaximalSeshadri.Bertini
noncomputable section
open KaehlerDifferential
variable {K A ι : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]

theorem critical_incidence_polynomial [Algebra.FiniteType K A]
    [Fintype ι] (v : ι → A) (a : Option ι → A)
    (hzero : a none + ∑ i, a (some i) * v i = 0)
    (hcritical : ∑ i, a (some i) • D K A (v i) = 0) :
    ∃ p : MvPolynomial (Option ι) K, p ≠ 0 ∧ IsNilpotent (MvPolynomial.aeval a p) := by
  classical
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let Q := minimalPrimes A
  let : Fintype Q := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  have hf : ∀ q : Q, ∃ p : MvPolynomial (Option ι) K,
      p ≠ 0 ∧ MvPolynomial.aeval a p ∈ q.val := by
    intro q
    let : q.val.IsPrime := q.property.isPrime
    let B := A ⧸ q.val
    let F := FractionRing B
    let : Algebra.EssFiniteType B F :=
      Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors B)
    let : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K B F
    obtain ⟨p, hp, he⟩ := critical_parameters_polynomial_image (L := F) v a hzero hcritical
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
open KaehlerDifferential
variable {K R A ι κ : Type*} [CommRing K] [CommRing R] [CommRing A]
  [Algebra K R] [Algebra K A] [Algebra R A] [IsScalarTower K R A]
  [Fintype ι] [Fintype κ]

lemma differential_expansion (b : Module.Basis κ R Ω[R⁄K]) (x : R) :
    D K A (algebraMap R A x) =
      ∑ j, algebraMap R A (b.repr (D K R x) j) •
        KaehlerDifferential.map K K R A (b j) := by
  have h := congrArg (KaehlerDifferential.map K K R A) (b.sum_repr (D K R x))
  simpa only [map_sum, map_smul, IsScalarTower.algebraMap_smul,
    KaehlerDifferential.map_D] using h.symm

lemma critical_of_coordinates (b : Module.Basis κ R Ω[R⁄K])
    (v : ι → R) (a : ι → A)
    (h : ∀ j, ∑ i, a i * algebraMap R A (b.repr (D K R (v i)) j) = 0) :
    ∑ i, a i • D K A (algebraMap R A (v i)) = 0 := by
  simp_rw [differential_expansion b, Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h, zero_smul, Finset.sum_const_zero]

end
noncomputable section
open KaehlerDifferential MvPolynomial
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

def universalSection (v : ι → R) : MvPolynomial (Option ι) R :=
  X none + ∑ i, X (some i) * C (v i)

def universalGradient (b : Module.Basis κ R Ω[R⁄K]) (v : ι → R)
    (j : κ) : MvPolynomial (Option ι) R :=
  ∑ i, X (some i) * C (b.repr (D K R (v i)) j)

def criticalIdeal (b : Module.Basis κ R Ω[R⁄K]) (v : ι → R) :
    Ideal (MvPolynomial (Option ι) R) :=
  Ideal.span (insert (universalSection v) (Set.range (universalGradient b v)))

theorem universal_critical_polynomial [Algebra.FiniteType K R]
    (b : Module.Basis κ R Ω[R⁄K]) (v : ι → R) :
    ∃ p : MvPolynomial (Option ι) K, p ≠ 0 ∧
      IsNilpotent (MvPolynomial.aeval (fun i =>
        algebraMap (MvPolynomial (Option ι) R)
          (MvPolynomial (Option ι) R ⧸ criticalIdeal b v) (X i)) p) := by
  let T := MvPolynomial (Option ι) R
  let A := T ⧸ criticalIdeal b v
  let a : Option ι → A := fun i => algebraMap T A (X i)
  have hC (r : R) : algebraMap T A (C r) = algebraMap R A r := rfl
  have hzero : a none + ∑ i, a (some i) * algebraMap R A (v i) = 0 := by
    have he : algebraMap T A (universalSection v) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
    simpa only [universalSection, map_add, map_sum, map_mul,
      hC, a] using he
  have hgrad : ∀ j, ∑ i, a (some i) *
      algebraMap R A (b.repr (D K R (v i)) j) = 0 := by
    intro j
    have he : algebraMap T A (universalGradient b v j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j)))
    simpa only [universalGradient, map_sum, map_mul,
      hC, a] using he
  exact critical_incidence_polynomial (fun i => algebraMap R A (v i)) a hzero
    (critical_of_coordinates b v (fun i => a (some i)) hgrad)

end
noncomputable section
open KaehlerDifferential MvPolynomial
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

def specializedSection (v : ι → R) (t : Option ι → K) : R :=
  algebraMap K R (t none) + ∑ i, algebraMap K R (t (some i)) * v i

def specializedGradient (b : Module.Basis κ R Ω[R⁄K]) (v : ι → R)
    (t : Option ι → K) (j : κ) : R :=
  ∑ i, algebraMap K R (t (some i)) * b.repr (D K R (v i)) j

omit [CharZero K] [Fintype κ] in

theorem critical_specialization_eq_top
    (b : Module.Basis κ R Ω[R⁄K]) (v : ι → R) (p : MvPolynomial (Option ι) K)
    (hp : IsNilpotent (MvPolynomial.aeval (fun i =>
        algebraMap (MvPolynomial (Option ι) R)
          (MvPolynomial (Option ι) R ⧸ criticalIdeal b v) (X i)) p))
    (t : Option ι → K) (ht : MvPolynomial.aeval t p ≠ 0) :
    Ideal.span (insert (specializedSection v t)
      (Set.range (specializedGradient b v t))) = ⊤ := by
  classical
  by_contra hne
  let J := Ideal.span (insert (specializedSection v t)
    (Set.range (specializedGradient b v t)))
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
  let : M.IsMaximal := hM
  let B := R ⧸ M
  let T := MvPolynomial (Option ι) R
  let A := T ⧸ criticalIdeal b v
  let φ : T →ₐ[K] B := (MvPolynomial.aeval (fun i => algebraMap K B (t i))).restrictScalars K
  have hφX (i : Option ι) : φ (X i) = algebraMap K B (t i) := MvPolynomial.aeval_X _ _
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
    have hψ (i : Option ι) : ψ (algebraMap T A (X i)) = algebraMap K B (t i) := by
      change φ (X i) = algebraMap K B (t i)
      exact hφX i
    rw [MvPolynomial.comp_aeval_apply, show (fun i =>
      ψ (algebraMap T A (X i))) = (fun i => algebraMap K B (t i)) from funext hψ] at h
    have he := MvPolynomial.comp_aeval_apply t (Algebra.ofId K B) p
    exact he ▸ h
  exact hspec.not_isUnit ((isUnit_iff_ne_zero.mpr ht).map (algebraMap K B))

end

noncomputable section
open KaehlerDifferential TensorProduct Algebra

theorem formallySmooth_principal_of_derivation
    {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (P : Algebra.Extension K S) [Algebra.FormallySmooth K P.Ring]
    (f : P.Ring) (hf : Ideal.span ({f} : Set P.Ring) = P.ker)
    (δ : Derivation K P.Ring S) (hδ : δ f = 1) :
    Algebra.FormallySmooth K S := by
  let g : P.Cotangent := Extension.Cotangent.mk ⟨f, hf ▸ Ideal.mem_span_singleton_self f⟩
  let l : P.CotangentSpace →ₗ[S] P.Cotangent :=
    (LinearMap.toSpanSingleton S P.Cotangent g).comp
      (LinearMap.liftBaseChange S δ.liftKaehlerDifferential)
  apply P.formallySmooth_iff_split_injection.mpr
  refine ⟨l, ?_⟩
  have hspan : Submodule.span S (Set.range (fun _ : Unit => g)) = ⊤ := by
    apply Extension.Cotangent.span_eq_top_of_span_eq_ker (fun _ : Unit => f)
    simpa using hf
  apply LinearMap.ext_on_range hspan
  intro i
  simp [l, g, hδ]

theorem formallySmooth_principal_of_gradient
    {K S ι : Type*} [CommRing K] [CommRing S] [Algebra K S] [Fintype ι]
    (P : Algebra.Extension K S) [Algebra.FormallySmooth K P.Ring]
    (b : Module.Basis ι P.Ring Ω[P.Ring⁄K]) (f : P.Ring)
    (hf : Ideal.span ({f} : Set P.Ring) = P.ker)
    (hgrad : Ideal.span (Set.range (fun i =>
      algebraMap P.Ring S (b.repr (D K P.Ring f) i))) = ⊤) :
    Algebra.FormallySmooth K S := by
  have hmem : (1 : S) ∈ Ideal.span (Set.range (fun i =>
      algebraMap P.Ring S (b.repr (D K P.Ring f) i))) := hgrad ▸ (show (1 : S) ∈ (⊤ : Ideal S) from trivial)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  let l : Ω[P.Ring⁄K] →ₗ[P.Ring] S := ∑ i, c i •
    ((Algebra.linearMap P.Ring S).comp (b.coord i))
  apply formallySmooth_principal_of_derivation P f hf (l.compDer (D K P.Ring))
  change l (D K P.Ring f) = 1
  simpa [l, Module.Basis.coord_apply] using hc

theorem formallySmooth_quotient_of_gradient
    {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R] [Fintype ι]
    [Algebra.FormallySmooth K R] (b : Module.Basis ι R Ω[R⁄K]) (f : R)
    (hgrad : Ideal.span (insert f (Set.range (fun i => b.repr (D K R f) i))) = ⊤) :
    Algebra.FormallySmooth K (R ⧸ Ideal.span ({f} : Set R)) := by
  let I := Ideal.span ({f} : Set R)
  let S := R ⧸ I
  let P : Algebra.Extension K S := Algebra.Extension.ofSurjective
    (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mk_surjective)
  let : Algebra.FormallySmooth K P.Ring := ‹Algebra.FormallySmooth K R›
  have hker : Ideal.span ({f} : Set P.Ring) = P.ker := (Ideal.mk_ker).symm
  have hgrad' : Ideal.span (Set.range (fun i =>
      algebraMap R S (b.repr (D K R f) i))) = ⊤ := by
    have h := congrArg (Ideal.map (Ideal.Quotient.mk I)) hgrad
    have hf : Ideal.Quotient.mk I f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
    simpa only [S, Ideal.Quotient.algebraMap_eq, Ideal.map_span, Set.image_insert_eq, ← Set.range_comp, Function.comp_def, hf,
      Ideal.span_insert_zero, Ideal.map_top] using h
  exact formallySmooth_principal_of_gradient P b f hker hgrad'

end

noncomputable section
open KaehlerDifferential MvPolynomial
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

omit [CharZero K] [Fintype κ] in
lemma specializedGradient_eq (b : Module.Basis κ R Ω[R⁄K]) (v : ι → R)
    (t : Option ι → K) (j : κ) :
    b.repr (D K R (specializedSection v t)) j = specializedGradient b v t j := by
  simp only [specializedSection, specializedGradient, map_add, map_sum,
    Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
    zero_add, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem affine_bertini_smooth [Algebra.Smooth K R]
    (b : Module.Basis κ R Ω[R⁄K]) (v : ι → R) :
    ∃ p : MvPolynomial (Option ι) K, p ≠ 0 ∧
      ∀ t : Option ι → K, MvPolynomial.aeval t p ≠ 0 →
        Algebra.Smooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) := by
  obtain ⟨p, hp, hcrit⟩ := universal_critical_polynomial b v
  refine ⟨p, hp, fun t ht => ?_⟩
  have hgrad := critical_specialization_eq_top b v p hcrit t ht
  rw [show specializedGradient b v t = (fun j =>
    b.repr (D K R (specializedSection v t)) j) from
      funext (fun j => (specializedGradient_eq b v t j).symm)] at hgrad
  let : Algebra.FormallySmooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) :=
    formallySmooth_quotient_of_gradient b (specializedSection v t) hgrad
  let : Algebra.FinitePresentation K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

end
end MaximalSeshadri.Bertini

end
end

end OAI
