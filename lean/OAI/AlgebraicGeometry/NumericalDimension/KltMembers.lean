import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.BoundaryDiscrepancies
import OAI.AlgebraicGeometry.NumericalDimension.GenericMembers

namespace OAI

/-! Klt Members. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct

namespace NumericalDimensionOne
noncomputable section

def IsKltBoundary {n : ℕ} (Y : CanonicalModel n) (Δ : QWeilDivisor Y.scheme) : Prop :=
  0 ≤ Δ ∧ IsQCartierDivisor (rationalWeilDivisor Y.canonical + Δ) ∧
  ∀ W : ComplexProjectiveVariety, IsSmoothNfold W n →
    ∀ f : W.scheme ⟶ Y.scheme, ∀ (_ : IsDominant f),
      IsProper f → IsBirationalMorphism f →
      ∀ hf : f ≫ Y.structureMap = W.structureMap,
        ∀ KW : WeilDivisor W.scheme,
          IsCanonicalDivisorOf (.of ℂ) W.structureMap n
            (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap f hf n Y.form) KW →
          ∀ P : QWeilDivisor W.scheme,
            IsQCartierPullback f (rationalWeilDivisor Y.canonical + Δ) P →
            ∀ p : PrimeDivisor W.scheme, -1 < (rationalWeilDivisor KW - P) p

lemma IsCartierPullback.zsmul {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {f : X ⟶ Y} [IsDominant f] {D : WeilDivisor Y} {P : WeilDivisor X}
    (hP : IsCartierPullback f D P) (z : ℤ) : IsCartierPullback f (z • D) (z • P) := by
  cases z with
  | ofNat m =>
      change IsCartierPullback f ((m : ℤ) • D) ((m : ℤ) • P)
      simpa only [natCast_zsmul] using hP.nsmul m
  | negSucc m => simpa only [negSucc_zsmul] using (hP.nsmul (m+1)).neg

lemma IsCartierPullback.rational {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {f : X ⟶ Y} [IsDominant f] {D : WeilDivisor Y} {P : WeilDivisor X}
    (hP : IsCartierPullback f D P) (hD : IsCartierDivisor D) :
    IsQCartierPullback f (rationalWeilDivisor D) (rationalWeilDivisor P) := by
  exact ⟨1,by decide,D,P,hD,by simp,by simp,hP⟩

lemma IsQCartierPullback.smul {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {f : X ⟶ Y} [IsDominant f] {D : QWeilDivisor Y} {P : QWeilDivisor X}
    (hP : IsQCartierPullback f D P) (t : ℚ) : IsQCartierPullback f (t • D) (t • P) := by
  obtain ⟨m,hm,A,B,hA,hAD,hBP,hAB⟩ := hP
  let M : CartierMultiple D := ⟨m,hm,⟨A,hA⟩,hAD⟩
  let N : CartierMultiple P := ⟨m,hm,⟨B,hAB.isCartier⟩,hBP⟩
  exact ⟨(M.smul t).denominator,(M.smul t).positive,(M.smul t).divisor.1,
    (N.smul t).divisor.1,(M.smul t).divisor.2,(M.smul t).equation,
    (N.smul t).equation,hAB.zsmul t.num⟩

theorem smooth_boundary_isKlt
    {n : ℕ} (Y : CanonicalModel n) (hY : IsSmoothNfold Y.toComplexProjectiveVariety n)
    (D : WeilDivisor Y.scheme) (hD : IsSmoothEffectiveCartierDivisor Y.toComplexProjectiveVariety D)
    (ε : ℚ) (hε : 0 ≤ ε) (hε1 : ε < 1) :
    IsKltBoundary Y (ε • rationalWeilDivisor D) := by
  have hK := canonicalModel_isCartier Y hY
  let M : CartierMultiple (rationalWeilDivisor Y.canonical) := ⟨1,by decide,⟨_,hK⟩,by simp⟩
  let N : CartierMultiple (rationalWeilDivisor D) := ⟨1,by decide,⟨_,hD.1⟩,by simp⟩
  let R := M.add (N.smul ε)
  refine ⟨?_,⟨R.denominator,R.positive,R.divisor.1,R.divisor.2,R.equation⟩,?_⟩
  · intro p
    change 0 ≤ ε * (D p : ℚ)
    exact mul_nonneg hε (by exact_mod_cast hD.2.1 p)
  intro W hW f hdom _hproper _hbir hf KW hKW Q hQ p
  let : IsDominant f := hdom
  let : StalkwiseNormal W.scheme := smoothNormal W hW
  obtain ⟨P,hP⟩ := exists_cartierPullback f Y.canonical hK
  obtain ⟨T,hT⟩ := exists_cartierPullback f D hD.1
  have he := hQ.unique ((hP.rational hK).add ((hT.rational hD.1).smul ε))
  rw [he]
  have ha := smooth_relative_canonical_effective W Y.toComplexProjectiveVariety n hW hY
    f hf Y.form KW Y.canonical hKW Y.canonical_of_form P hP p
  have hb := smooth_boundary_discrepancy_bound W Y.toComplexProjectiveVariety n hW hY
    f hf Y.form KW Y.canonical hKW Y.canonical_of_form P hP D hD T hT p
  have haQ : (0 : ℚ) ≤ (KW p : ℚ) - (P p : ℚ) := by exact_mod_cast ha
  have hbQ : (T p : ℚ) ≤ (KW p : ℚ) - (P p : ℚ) + 1 := by exact_mod_cast hb
  have hm := mul_le_mul_of_nonneg_left hbQ hε
  have hs : 0 < (1-ε)*((KW p : ℚ)-(P p : ℚ)+1) :=
    mul_pos (sub_pos.mpr hε1) (by linarith)
  change (-1 : ℚ) < (KW p : ℚ) - ((P p : ℚ) + ε*(T p : ℚ))
  nlinarith
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section
universe u

lemma constructible_constant_near_generic
    {T : Type*} [TopologicalSpace T] {g : T}
    (hg : IsGenericPoint g Set.univ) {S : Set T} (hS : IsConstructible S) :
    ∃ U : Opens T, g ∈ U ∧ ∀ x ∈ U, x ∈ S ↔ g ∈ S := by
  classical
  induction hS using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    by_cases h : g ∈ U
    · exact ⟨⟨U,hU⟩,h,fun x hx => iff_of_true hx h⟩
    · refine ⟨⊤,trivial,fun x _ => iff_of_false (fun hx => h ?_) h⟩
      exact (hg.specializes trivial).mem_open hU hx
  | union s hs t ht ihs iht =>
    obtain ⟨U,hU,hUs⟩ := ihs
    obtain ⟨V,hV,hVt⟩ := iht
    refine ⟨U ⊓ V,⟨hU,hV⟩,fun x hx => ?_⟩
    exact or_congr (hUs x hx.1) (hVt x hx.2)
  | compl s hs ih =>
    obtain ⟨U,hU,hUs⟩ := ih
    exact ⟨U,hU,fun x hx => not_congr (hUs x hx)⟩

theorem finiteType_generic_smooth_open
    {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
    [IsIntegral Y] [NoetherianSpace X] [NoetherianSpace Y]
    (f : X ⟶ Y) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFinitePresentation f] [LocallyOfFiniteType sY]
    [Smooth (f ≫ sY)] :
    ∃ U : Y.Opens, genericPoint Y ∈ U ∧ f ⁻¹ᵁ U ≤ f.smoothLocus := by
  let B : Set X := (f.smoothLocus : Set X)ᶜ
  have hB : IsConstructible B :=
    ((NoetherianSpace.isCompact (f.smoothLocus : Set X)).isConstructible
      f.smoothLocus.isOpen).compl
  obtain ⟨U,hU,hc⟩ := constructible_constant_near_generic (genericPoint_spec Y)
    (f.isConstructible_image hB)
  refine ⟨U,hU,fun x hx => ?_⟩
  by_contra h
  have hh := (hc (f x) hx).mp (Set.mem_image_of_mem f h)
  obtain ⟨z,hz,hzg⟩ := hh
  exact hz (smooth_at_generic_fiber f sY z hzg)
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
universe u v

theorem exists_avoiding_countable_polynomials
    {k : Type u} [Field k] [Uncountable k]
    {ι : Type v} [Countable ι] (n : ℕ)
    (p : ι → MvPolynomial (Fin n) k) (hp : ∀ i, p i ≠ 0) :
    ∃ a : Fin n → k, ∀ i, MvPolynomial.eval a (p i) ≠ 0 := by
  classical
  induction n with
  | zero =>
    let a : Fin 0 → k := Fin.elim0
    refine ⟨a,fun i hi => hp i ?_⟩
    have hinj : Function.Injective (MvPolynomial.aeval a :
        MvPolynomial (Fin 0) k →ₐ[k] k) :=
      MvPolynomial.aeval_injective_iff_of_isEmpty.mpr (RingHom.id k).injective
    apply hinj
    simpa using hi
  | succ n ih =>
    let q (i : ι) := MvPolynomial.finSuccEquiv k n (p i)
    have hq (i : ι) : q i ≠ 0 := by
      exact fun h => hp i ((MvPolynomial.finSuccEquiv k n).injective (by simpa [q] using h))
    obtain ⟨a,ha⟩ := ih (fun i => (q i).leadingCoeff)
      (fun i => Polynomial.leadingCoeff_ne_zero.mpr (hq i))
    let q' (i : ι) := Polynomial.map (MvPolynomial.eval a) (q i)
    have hq' (i : ι) : q' i ≠ 0 := by
      intro h
      have hc := congrArg (fun f : Polynomial k => f.coeff (q i).natDegree) h
      apply ha i
      simpa only [q',Polynomial.coeff_map,Polynomial.coeff_zero,
        Polynomial.coeff_natDegree] using hc
    have hc : (⋃ i, {x : k | Polynomial.IsRoot (q' i) x}).Countable :=
      Set.countable_iUnion (fun i => (Polynomial.finite_setOfPred_isRoot (hq' i)).countable)
    have hn : ∃ x : k, x ∉ ⋃ i, {x : k | Polynomial.IsRoot (q' i) x} := by
      by_contra! h
      exact Set.not_countable_univ (hc.mono (fun x _ => h x))
    obtain ⟨x,hx⟩ := hn
    refine ⟨Fin.cons x a,fun i hi => hx ?_⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i,?_⟩
    change Polynomial.eval x (q' i) = 0
    simpa only [MvPolynomial.eval_eq_eval_mv_eval',q',q] using hi
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section
lemma exists_rational_tuple_in_countable_spec_opens
    {k : Type} [Field k] [Uncountable k] {ι : Type} [Countable ι]
    (n : ℕ) (U : ι → (Spec (.of (MvPolynomial (Fin n) k))).Opens)
    (hU : ∀ i, genericPoint (Spec (.of (MvPolynomial (Fin n) k))) ∈ U i) :
    ∃ a : Fin n → k, ∀ i,
      Set.range (Spec.map (CommRingCat.ofHom (MvPolynomial.eval a))) ⊆ U i := by
  classical
  have hs (i : ι) : ∃ f : MvPolynomial (Fin n) k, f ≠ 0 ∧
      ∀ x : Spec (.of (MvPolynomial (Fin n) k)), x ∈ PrimeSpectrum.basicOpen f → x ∈ U i := by
    obtain ⟨_,⟨f,rfl⟩,hf,hfU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp (U i).isOpen _ (hU i)
    refine ⟨f,?_,hfU⟩
    rw [genericPoint_eq_bot_of_affine] at hf
    change f ∉ (⊥ : PrimeSpectrum (MvPolynomial (Fin n) k)).asIdeal at hf
    simpa only [PrimeSpectrum.asIdeal_bot,Ideal.mem_bot] using hf
  choose f hf hfU using hs
  obtain ⟨a,ha⟩ := exists_avoiding_countable_polynomials n f hf
  refine ⟨a,fun i => ?_⟩
  rintro _ ⟨x,rfl⟩
  apply hfU i
  let point : PrimeSpectrum k := x
  change MvPolynomial.eval a (f i) ∉ point.asIdeal
  simpa only [Ideal.eq_bot_of_prime point.asIdeal,Ideal.mem_bot] using ha i

theorem exists_rational_point_in_countable_affine_opens
    {k : Type} [Field k] [Uncountable k] {ι : Type} [Countable ι]
    (n : ℕ) (U : ι → (𝔸(Fin n;Spec (.of k))).Opens)
    (hU : ∀ i, genericPoint (𝔸(Fin n;Spec (.of k))) ∈ U i) :
    ∃ p : Spec (.of k) ⟶ 𝔸(Fin n;Spec (.of k)),
      p ≫ 𝔸(Fin n;Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ ∧
      ∀ i, Set.range p ⊆ U i := by
  let e := AffineSpace.SpecIso (Fin n) (.of k)
  obtain ⟨a,ha⟩ := exists_rational_tuple_in_countable_spec_opens n
    (fun i => e.inv ⁻¹ᵁ U i) (fun i => by
      change e.inv (genericPoint _) ∈ U i
      rw [genericPoint_eq_of_isOpenImmersion e.inv]
      exact hU i)
  let q := Spec.map (CommRingCat.ofHom (MvPolynomial.eval a))
  refine ⟨q ≫ e.inv,?_,?_⟩
  · rw [Category.assoc,AffineSpace.SpecIso_inv_over,← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((MvPolynomial.eval a).comp MvPolynomial.C)) = 𝟙 _
    have he : (MvPolynomial.eval a).comp MvPolynomial.C = RingHom.id k := by
      ext x; simp
    rw [he]
    exact Spec.map_id _
  · intro i
    rintro _ ⟨x,rfl⟩
    exact ha i ⟨x,rfl⟩
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section

theorem exists_smooth_fiber_in_countable_opens
    {k : Type} [Field k] [CharZero k] [Uncountable k]
    {X : Scheme} [NoetherianSpace X] {ι : Type} [Countable ι]
    (n : ℕ) (f : X ⟶ 𝔸(Fin n;Spec (.of k)))
    [LocallyOfFinitePresentation f]
    [Smooth (f ≫ 𝔸(Fin n;Spec (.of k)) ↘ Spec (.of k))]
    (V : ι → (𝔸(Fin n;Spec (.of k))).Opens)
    (hV : ∀ i, genericPoint (𝔸(Fin n;Spec (.of k))) ∈ V i) :
    ∃ p : Spec (.of k) ⟶ 𝔸(Fin n;Spec (.of k)),
      p ≫ 𝔸(Fin n;Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ ∧
      (∀ i, Set.range p ⊆ V i) ∧ Smooth (pullback.snd f p) := by
  have : IsLocallyNoetherian (𝔸(Fin n;Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (𝔸(Fin n;Spec (.of k)) ↘ Spec (.of k))
  have : NoetherianSpace (𝔸(Fin n;Spec (.of k))) :=
    (noetherianSpace_iff_of_homeomorph (AffineSpace.SpecIso (Fin n) (.of k)).hom.homeomorph).mpr inferInstance
  obtain ⟨U,hU,hpre⟩ := finiteType_generic_smooth_open f
    (𝔸(Fin n;Spec (.of k)) ↘ Spec (.of k))
  let W : Option ι → (𝔸(Fin n;Spec (.of k))).Opens := fun i => i.elim U V
  have hW (i : Option ι) : genericPoint _ ∈ W i := by
    cases i with
    | none => exact hU
    | some i => exact hV i
  obtain ⟨p,hp,hpW⟩ := exists_rational_point_in_countable_affine_opens n W hW
  have : Smooth (f ∣_ U) := smooth_morphismRestrict_of_preimage_le f U hpre
  have ha : Set.range p ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact hpW none
  let b := IsOpenImmersion.lift U.ι p ha
  have hb : b ≫ U.ι = p := IsOpenImmersion.lift_fac U.ι p ha
  refine ⟨p,hp,(fun i => hpW (some i)),?_⟩
  have hpb := (IsPullback.of_hasPullback (f ∣_ U) b).paste_horiz
    (isPullback_morphismRestrict f U).flip
  rw [hb] at hpb
  let e := hpb.isoIsPullback _ _ (IsPullback.of_hasPullback f p)
  have he : e.hom ≫ pullback.snd f p = pullback.snd (f ∣_ U) b :=
    hpb.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f p)
  have : Smooth (e.hom ≫ pullback.snd f p) := by
    rw [he]
    infer_instance
  have : Smooth (e.inv ≫ e.hom ≫ pullback.snd f p) := inferInstance
  simpa using this
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section

theorem exists_linear_nonvanishing_parameter_open
    {k K : Type} [Field k] [Field K] [Algebra k K]
    {n : Type} [Fintype n] (s : n → K) (i : n) (hi : s i ≠ 0) :
    ∃ U : (𝔸(n;Spec (.of k))).Opens,
      genericPoint _ ∈ U ∧
      ∀ p : Spec (.of k) ⟶ 𝔸(n;Spec (.of k)),
        p ≫ 𝔸(n;Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ →
        Set.range p ⊆ U → parameterLinearCombination s p ≠ 0 := by
  classical
  obtain ⟨L,hL⟩ := Module.Projective.exists_dual_eq_one k hi
  let r : n → Γ(Spec (.of k),⊤) := fun j => (Scheme.ΓSpecIso (.of k)).inv (L (s j))
  have hr : r i = 1 := by simp [r,hL]
  let U := (𝔸(n;Spec (.of k))).basicOpen (universalLinearSection r)
  refine ⟨U,generic_mem_linear_parameter_open r i hr,?_⟩
  intro p hp hpU hz
  have hne := appTop_ne_zero_of_range_basicOpen p (universalLinearSection r) hpU
  apply hne
  apply (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective
  rw [map_zero]
  change (Scheme.ΓSpecIso (.of k)).hom
    (p.appTop (universalLinearSection (fun j => (Scheme.ΓSpecIso (.of k)).inv (L (s j))))) = 0
  rw [parameter_evaluate_linear s L p hp,hz,map_zero]
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section
lemma linearMemberSection_evaluate
    {k K n : Type} [Field k] [Field K] [Fintype n]
    {V : Scheme} (sV : V ⟶ Spec (.of k))
    (p : Spec (.of k) ⟶ 𝔸(n;Spec (.of k))) (r : n → Γ(V,⊤))
    (φ : Γ(V,⊤) →+* K) :
    let : Algebra k K := (φ.comp (sV.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)).toAlgebra
    φ (linearMemberSection sV p r) = parameterLinearCombination (φ ∘ r) p := by
  let : Algebra k K := (φ.comp (sV.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)).toAlgebra
  simp only [linearMemberSection,parameterLinearCombination,map_sum,map_mul,
    Function.comp_apply,Algebra.smul_def,parameterCoefficient,RingHom.algebraMap_toAlgebra,
    RingHom.comp_apply,Iso.hom_inv_id_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section

theorem exists_parameter_open_avoiding_point
    {k n : Type} [Field k] [Fintype n] {V : Scheme} [IsAffine V]
    (sV : V ⟶ Spec (.of k)) (r : n → Γ(V,⊤)) (i : n) (hi : r i = 1) (x : V) :
    ∃ U : (𝔸(n;Spec (.of k))).Opens, genericPoint _ ∈ U ∧
      ∀ p : Spec (.of k) ⟶ 𝔸(n;Spec (.of k)),
        p ≫ 𝔸(n;Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ → Set.range p ⊆ U →
        x ∉ (Scheme.IdealSheafData.ofIdealTop
          (Ideal.span {linearMemberSection sV p r})).support := by
  let φ : Γ(V,⊤) →+* V.residueField x :=
    (V.residue x).hom.comp (V.presheaf.germ ⊤ x trivial).hom
  let : Algebra k (V.residueField x) :=
    (φ.comp (sV.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)).toAlgebra
  have hi' : (φ ∘ r) i ≠ 0 := by simp [hi]
  obtain ⟨U,hU,hUp⟩ := exists_linear_nonvanishing_parameter_open (k := k) (φ ∘ r) i hi'
  refine ⟨U,hU,fun p hp hpU => ?_⟩
  have hn : φ (linearMemberSection sV p r) ≠ 0 := by
    rw [linearMemberSection_evaluate]
    exact hUp p hp hpU
  have hx : x ∈ V.basicOpen (linearMemberSection sV p r) := by
    rw [Scheme.mem_basicOpen_top]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hn
  change x ∉ ((Scheme.IdealSheafData.ofIdealTop
    (Ideal.span {linearMemberSection sV p r})).support : Set V)
  rw [Scheme.IdealSheafData.coe_support_ofIdealTop,Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton]
  exact fun h => h hx
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section

theorem incidence_parameter_open_avoiding_point
    {k n : Type} [Field k] [Fintype n] {X : Scheme}
    (sX : X ⟶ Spec (.of k)) (V : X.OpenCover) [∀ i, IsAffine (V.X i)]
    (r : ∀ i, n → Γ(V.X i,⊤)) (hn : ∀ i, ∃ j, r i j = 1)
    (J : 𝔸(n;X).IdealSheafData)
    (hJ : ∀ i, J.comap (AffineSpace.map n (V.f i)) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (r i)}))
    (x : X) :
    ∃ U : (𝔸(n;Spec (.of k))).Opens, genericPoint _ ∈ U ∧
      ∀ p : Spec (.of k) ⟶ 𝔸(n;Spec (.of k)),
        p ≫ 𝔸(n;Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ → Set.range p ⊆ U →
        x ∉ (J.comap (parameterSection sX p)).support := by
  let i := V.idx x
  obtain ⟨y,hy⟩ := V.covers x
  obtain ⟨a,ha⟩ := hn i
  obtain ⟨U,hU,hUp⟩ := exists_parameter_open_avoiding_point (V.f i ≫ sX) (r i) a ha y
  refine ⟨U,hU,fun p hp hpU hx => ?_⟩
  apply hUp p hp hpU
  rw [← parameter_member_chart (V.f i) sX p J (r i) (hJ i),
    Scheme.IdealSheafData.support_comap]
  change V.f i y ∈ (J.comap (parameterSection sX p)).support
  change (V.f (V.idx x)) y ∈ (J.comap (parameterSection sX p)).support
  rwa [hy]
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section
universe u

theorem incidence_smooth_baseChange
    {n : Type u} {X Y : Scheme.{u}} (h : Y ⟶ X)
    (J : 𝔸(n;X).IdealSheafData) [Smooth (J.subschemeι ≫ 𝔸(n;X) ↘ X)] :
    Smooth ((J.comap (AffineSpace.map n h)).subschemeι ≫ 𝔸(n;Y) ↘ Y) := by
  let a := AffineSpace.map n h
  have hp := (IsPullback.of_hasPullback a J.subschemeι).flip.paste_vert
    (AffineSpace.isPullback_map (n := n) h)
  let e := hp.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)
  have he : e.hom ≫ pullback.snd (J.subschemeι ≫ 𝔸(n;X) ↘ X) h =
      pullback.fst a J.subschemeι ≫ 𝔸(n;Y) ↘ Y :=
    hp.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback _ _)
  have hs : Smooth (pullback.fst a J.subschemeι ≫ 𝔸(n;Y) ↘ Y) := by
    rw [← he]
    infer_instance
  change Smooth ((J.comap a).subschemeι ≫ 𝔸(n;Y) ↘ Y)
  rw [← J.comapIso_hom_fst a,Category.assoc]
  infer_instance
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section

theorem exists_very_general_incidence_member
    {k : Type} [Field k] [CharZero k] [Uncountable k]
    {n : ℕ} {X : Scheme} [NoetherianSpace X]
    (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (J : 𝔸(Fin n;X).IdealSheafData) [Smooth (J.subschemeι ≫ 𝔸(Fin n;X) ↘ X)]
    {ι : Type} [Countable ι] (V : ι → (𝔸(Fin n;Spec (.of k))).Opens)
    (hV : ∀ i, genericPoint _ ∈ V i) :
    ∃ p : Spec (.of k) ⟶ 𝔸(Fin n;Spec (.of k)),
      p ≫ 𝔸(Fin n;Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ ∧
      (∀ i, Set.range p ⊆ V i) ∧
      Smooth ((J.comap (parameterSection sX p)).subschemeι ≫ sX) := by
  let f := J.subschemeι ≫ AffineSpace.map (Fin n) sX
  let sA := 𝔸(Fin n;Spec (.of k)) ↘ Spec (.of k)
  have hfs : f ≫ sA = (J.subschemeι ≫ 𝔸(Fin n;X) ↘ X) ≫ sX := by
    simp only [f,sA,Category.assoc,AffineSpace.map_over]
  have : Smooth (f ≫ sA) := by rw [hfs]; infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian (𝔸(Fin n;X)) :=
    LocallyOfFiniteType.isLocallyNoetherian (𝔸(Fin n;X) ↘ X)
  have : CompactSpace (𝔸(Fin n;X)) :=
    QuasiCompact.compactSpace_of_compactSpace (𝔸(Fin n;X) ↘ X)
  have : IsLocallyNoetherian J.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  have : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
  have : IsNoetherian J.subscheme := ⟨⟩
  have : IsLocallyNoetherian (𝔸(Fin n;Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian sA
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f sA
  have : LocallyOfFinitePresentation f := inferInstance
  obtain ⟨p,hp,hpV,hsm⟩ := exists_smooth_fiber_in_countable_opens n f V hV
  exact ⟨p,hp,hpV,smooth_parameter_member sX p hp J⟩
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section

lemma parameter_member_comap {n : Type*} {V X S : Scheme}
    (g : V ⟶ X) (f : X ⟶ S) (p : S ⟶ 𝔸(n;S)) (J : 𝔸(n;X).IdealSheafData) :
    (J.comap (parameterSection f p)).comap g =
      (J.comap (AffineSpace.map n g)).comap (parameterSection (g ≫ f) p) := by
  rw [← Scheme.IdealSheafData.comap_comp, parameterSection_naturality,
    Scheme.IdealSheafData.comap_comp]

theorem exists_very_general_incidence_member_on_open
    {k : Type} [Field k] [CharZero k] [Uncountable k]
    {n : ℕ} {X : Scheme} [NoetherianSpace X]
    (sX : X ⟶ Spec (.of k)) (U : X.Opens) [AlgebraicGeometry.Smooth (U.ι ≫ sX)]
    (J : 𝔸(Fin n;X).IdealSheafData) [AlgebraicGeometry.Smooth (J.subschemeι ≫ 𝔸(Fin n;X) ↘ X)]
    {ι : Type} [Countable ι] (V : ι → (𝔸(Fin n;Spec (.of k))).Opens)
    (hV : ∀ i, genericPoint _ ∈ V i) :
    ∃ p : Spec (.of k) ⟶ 𝔸(Fin n;Spec (.of k)),
      p ≫ 𝔸(Fin n;Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ ∧
      (∀ i, Set.range p ⊆ V i) ∧
      AlgebraicGeometry.Smooth (((J.comap (parameterSection sX p)).comap U.ι).subschemeι ≫ (U.ι ≫ sX)) := by
  have : NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let JU : 𝔸(Fin n;U).IdealSheafData := J.comap (AffineSpace.map (Fin n) U.ι)
  have : AlgebraicGeometry.Smooth (JU.subschemeι ≫ 𝔸(Fin n;U) ↘ U) := incidence_smooth_baseChange U.ι J
  obtain ⟨p,hp,hpV,hsm⟩ := exists_very_general_incidence_member (U.ι ≫ sX) JU V hV
  refine ⟨p,hp,hpV,?_⟩
  have hi : (J.comap (parameterSection sX p)).comap U.ι =
      JU.comap (parameterSection (U.ι ≫ sX) p) := parameter_member_comap U.ι sX p J
  exact (congrArg
    (fun ideal : (U : Scheme).IdealSheafData => AlgebraicGeometry.Smooth (ideal.subschemeι ≫ (U.ι ≫ sX)))
    hi).mpr hsm
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
universe u

theorem closed_set_finite_generics {X : Scheme.{u}} [NoetherianSpace X]
    {Z : Set X} (hZ : IsClosed Z) :
    ∃ G : Finset X, ∀ x, x ∈ Z ↔ ∃ g ∈ G, x ∈ closure {g} := by
  classical
  obtain ⟨S,hSf,hSc,hSi,hSZ⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  let : Fintype S := hSf.fintype
  choose g hg using fun T : S => QuasiSober.sober (hSi T T.2) (hSc T T.2)
  refine ⟨Finset.univ.image g,fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨T,hT,hxT⟩ := Set.mem_sUnion.mp (hSZ ▸ hx)
    refine ⟨g ⟨T,hT⟩,Finset.mem_image.mpr ⟨⟨T,hT⟩,Finset.mem_univ _,rfl⟩,?_⟩
    rw [hg ⟨T,hT⟩]
    exact hxT
  · rintro ⟨z,hz,hxz⟩
    obtain ⟨T,_,rfl⟩ := Finset.mem_image.mp hz
    rw [hg T] at hxz
    rw [hSZ]
    exact Set.mem_sUnion.mpr ⟨T,T.2,hxz⟩

end NumericalDimensionOne

end OAI
