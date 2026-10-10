import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CurveProjection
import OAI.AlgebraicGeometry.NumericalDimension.FixedDivisors

namespace OAI

/-! Canonical Chains. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem surface_prime_degree_at_stalk_iso
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [StalkwiseNormal X] [StalkwiseNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX]
    (sY : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sY] [IsProper sY]
    (f : X ⟶ Y) [IsProper f] [IsDominant f] (hfs : f ≫ sY = sX)
    (q : PrimeDivisor X) [IsIso (f.stalkMap q.1)]
    (hp : Order.coheight (f q.1) = 1)
    (D : cartierDivisors (X := Y)) (P : cartierDivisors (X := X))
    (hP : IsCartierPullback f D.1 P.1) :
    surfaceCartierPrimeDegree sX P q = surfaceCartierPrimeDegree sY D ⟨f q.1,hp⟩ := by
  let Tq := pointClosure q.1
  let Tp := pointClosure (f q.1)
  let nq := Tq.fromSpecStalk (genericPoint Tq)
  let np := Tp.fromSpecStalk (genericPoint Tp)
  let gq := nq.fromNormalization ≫ pointClosureι q.1
  let gp := np.fromNormalization ≫ pointClosureι (f q.1)
  let sc := gq ≫ sX
  let st := gp ≫ sY
  have : SmoothOfRelativeDimension 1 sc := by
    simpa only [sc,gq,Category.assoc] using surface_prime_normalization_smooth sX q.1 q.2
  have : IsProper sc := by
    simpa only [sc,gq,Category.assoc] using surface_prime_normalization_proper sX q.1
  have : IsLocallyNoetherian nq.normalization := LocallyOfFiniteType.isLocallyNoetherian sc
  have : CompactSpace nq.normalization := QuasiCompact.compactSpace_of_compactSpace sc
  have : AlgebraicGeometry.IsNoetherian nq.normalization := ⟨⟩
  have : SmoothOfRelativeDimension 1 st := by
    simpa only [st,gp,Category.assoc] using surface_prime_normalization_smooth sY (f q.1) hp
  have : IsProper st := by
    simpa only [st,gp,Category.assoc] using surface_prime_normalization_proper sY (f q.1)
  have : IsLocallyNoetherian np.normalization := LocallyOfFiniteType.isLocallyNoetherian st
  have : CompactSpace np.normalization := QuasiCompact.compactSpace_of_compactSpace st
  have : Nontrivial Tp := surface_pointClosure_nontrivial sY (f q.1) hp
  have : IsProper (pointClosureι (f q.1) ≫ sY) := inferInstance
  have : IsProper (np.fromNormalization ≫ (pointClosureι (f q.1) ≫ sY)) := by
    simpa only [st,gp,Category.assoc] using (inferInstance : IsProper st)
  have : IsProper np.fromNormalization :=
    IsProper.of_comp np.fromNormalization (pointClosureι (f q.1) ≫ sY)
  obtain ⟨r,hr,_hrproper,hrdom,hrbij⟩ := pointClosure_map_functionField_bijective f q.1
  let g := nq.fromNormalization ≫ r
  have hgov : g ≫ (pointClosureι (f q.1) ≫ sY) = sc := by
    dsimp only [g,sc,gq]
    simp only [Category.assoc]
    rw [← Category.assoc r (pointClosureι (f q.1)) sY,hr,Category.assoc,hfs]
  obtain ⟨τ,hτ,hτfin,hτdom⟩ := curve_lift_through_proper_functionField_iso sc
    (pointClosureι (f q.1) ≫ sY) np.fromNormalization
    genericNormalization_bijective_functionField g hgov
  have hgbij : Function.Bijective (dominantFunctionFieldMap g) :=
    dominantFunctionFieldMap_bijective_comp nq.fromNormalization r
      genericNormalization_bijective_functionField hrbij
  have hcompbij : Function.Bijective (dominantFunctionFieldMap (τ ≫ np.fromNormalization)) := by
    simpa only [hτ] using hgbij
  have hd : curveFieldDegree τ = 1 := curveFieldDegree_eq_one τ
    (dominantFunctionFieldMap_bijective_of_comp τ np.fromNormalization hcompbij)
  have he : τ ≫ gp = gq ≫ f := by
    dsimp only [gp,gq]
    rw [← Category.assoc,hτ]
    dsimp only [g]
    rw [Category.assoc,hr,← Category.assoc]
  change properCurveDegree gq P = properCurveDegree gp D
  calc
    _ = properCurveDegree (gq ≫ f) D := properCurveDegree_ambientPullback sc gq f D P.1 hP
    _ = properCurveDegree (τ ≫ gp) D := congrArg (fun u => properCurveDegree u D) he.symm
    _ = (curveFieldDegree τ : ℤ) * properCurveDegree gp D :=
      properCurveDegree_comp_finite sc st τ gp D
    _ = _ := by rw [hd,Nat.cast_one,one_mul]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma order_dominantFunctionFieldMap_of_stalk_iso
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsDominant f] (q : PrimeDivisor X)
    [IsIso (f.stalkMap q.1)] (hp : Order.coheight (f q.1) = 1)
    (z : Y.functionField) (hz : z ≠ 0) :
    X.ord (dominantFunctionFieldMap f z) q.1 = Y.ord z (f q.1) := by
  let e := (asIso (f.stalkMap q.1)).commRingCatIsoToRingEquiv
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective (Y.presheaf.stalk (f q.1)) z
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha : a ≠ 0 := by intro h; simp only [h,map_zero,zero_div] at hz; exact hz rfl
  have hbY : algebraMap (Y.presheaf.stalk (f q.1)) Y.functionField b ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective (Y.presheaf.stalk (f q.1)) Y.functionField).ne hb
  have haY : algebraMap (Y.presheaf.stalk (f q.1)) Y.functionField a ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective (Y.presheaf.stalk (f q.1)) Y.functionField).ne ha
  have ho (v : Y.presheaf.stalk (f q.1)) (hv : v ≠ 0) :
      X.ord (dominantFunctionFieldMap f (algebraMap _ Y.functionField v)) q.1 =
        Y.ord (algebraMap _ Y.functionField v) (f q.1) := by
    rw [dominantFunctionFieldMap_algebraMap]
    have hv' : f.stalkMap q.1 v ≠ 0 := by
      change e v ≠ 0
      simpa only [map_zero] using e.injective.ne hv
    rw [scheme_order_of_stalk_element _ q.2 _ hv',
      scheme_order_of_stalk_element _ hp _ hv]
    exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (ringOrder_equiv e v)
  rw [map_div₀,order_div ((map_ne_zero _).mpr haY) ((map_ne_zero _).mpr hbY),
    order_div haY hbY,ho a ha,ho b hb]
lemma IsCartierPullback.coeff_eq_of_stalk_iso
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsDominant f] (q : PrimeDivisor X)
    [IsIso (f.stalkMap q.1)] (hp : Order.coheight (f q.1) = 1)
    {D : WeilDivisor Y} {P : WeilDivisor X} (hP : IsCartierPullback f D P) :
    P q = D ⟨f q.1,hp⟩ := by
  obtain ⟨U,_hU,hqU,z,hz,hDz,hPz⟩ := hP q.1
  exact (hPz q hqU).trans ((order_dominantFunctionFieldMap_of_stalk_iso f q hp z hz).trans
    (hDz ⟨f q.1,hp⟩ hqU).symm)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem surfaceIntersection_pullback
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [StalkwiseNormal X] [StalkwiseNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX]
    (sY : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sY] [IsProper sY]
    (f : X ⟶ Y) [IsProper f] [IsDominant f] (hf : IsBirationalMorphism f)
    (hfs : f ≫ sY = sX)
    (D E : cartierDivisors (X := Y)) (P Q : cartierDivisors (X := X))
    (hP : IsCartierPullback f D.1 P.1) (hQ : IsCartierPullback f E.1 Q.1) :
    surfaceIntersection sX P Q = surfaceIntersection sY D E := by
  classical
  choose l hl hiso huniq using exists_unique_prime_over_of_proper_birational f hf
  have linj : Function.Injective l := by
    intro a b hab
    apply Subtype.ext
    exact (hl a).symm.trans ((congrArg (fun q : PrimeDivisor X => f q.1) hab).trans (hl b))
  have hcoeff (p : PrimeDivisor Y) : P.1 (l p) = D.1 p := by
    have : IsIso (f.stalkMap (l p).1) := hiso p
    have hp : Order.coheight (f (l p).1) = 1 := by rw [hl p]; exact p.2
    have hh := hP.coeff_eq_of_stalk_iso f (l p) hp
    have he : (⟨f (l p).1,hp⟩ : PrimeDivisor Y) = p := Subtype.ext (hl p)
    rw [he] at hh
    exact hh
  have hdeg (p : PrimeDivisor Y) :
      surfaceCartierPrimeDegree sX Q (l p) = surfaceCartierPrimeDegree sY E p := by
    have : IsIso (f.stalkMap (l p).1) := hiso p
    have hp : Order.coheight (f (l p).1) = 1 := by rw [hl p]; exact p.2
    have hh := surface_prime_degree_at_stalk_iso sX sY f hfs (l p) hp E Q hQ
    have he : (⟨f (l p).1,hp⟩ : PrimeDivisor Y) = p := Subtype.ext (hl p)
    rw [he] at hh
    exact hh
  let S : Finset (PrimeDivisor X) := P.1.support ∪ D.1.support.image l
  have hzero (q : PrimeDivisor X) (hq : q ∉ D.1.support.image l) :
      P.1 q * surfaceCartierPrimeDegree sX Q q = 0 := by
    by_cases hp : Order.coheight (f q.1) = 1
    · let p : PrimeDivisor Y := ⟨f q.1,hp⟩
      have he : q = l p := Subtype.ext (huniq p q.1 rfl)
      have hD : D.1 p = 0 := by
        by_contra hn
        exact hq (Finset.mem_image.mpr ⟨p,Finsupp.mem_support_iff.mpr hn,he.symm⟩)
      rw [he,hcoeff,hD,zero_mul]
    · rw [surfaceCartierPrimeDegree_contracted sX Q hQ q
        (surface_prime_contracted_of_not_prime sY f hf q hp),mul_zero]
  unfold surfaceIntersection Finsupp.sum
  change (∑ q ∈ P.1.support, P.1 q * surfaceCartierPrimeDegree sX Q q) =
    ∑ p ∈ D.1.support, D.1 p * surfaceCartierPrimeDegree sY E p
  calc
    _ = ∑ q ∈ S, P.1 q * surfaceCartierPrimeDegree sX Q q := by
      apply Finset.sum_subset Finset.subset_union_left
      intro q _hq hn
      rw [Finsupp.notMem_support_iff.mp hn,zero_mul]
    _ = ∑ q ∈ D.1.support.image l, P.1 q * surfaceCartierPrimeDegree sX Q q := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro q _hq hn
      exact hzero q hn
    _ = ∑ p ∈ D.1.support, P.1 (l p) * surfaceCartierPrimeDegree sX Q (l p) := by
      exact Finset.sum_image (fun _ _ _ _ h => linj h)
    _ = _ := Finset.sum_congr rfl (fun p _ => by rw [hcoeff p,hdeg p])
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
section
universe u
variable (k : CommRingCat.{u}) {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
lemma rationalTopFormPullback_comp
    (sX : X ⟶ Spec k) (sY : Y ⟶ Spec k) (sZ : Z ⟶ Spec k)
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g]
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (n : ℕ) (ω : rationalTopForms k sZ n) :
    rationalTopFormPullback k sX sZ (f ≫ g) (by rw [Category.assoc,hg,hf]) n ω =
      rationalTopFormPullback k sX sY f hf n (rationalTopFormPullback k sY sZ g hg n ω) := by
  let := schemeFieldAlgebra k sX
  let := schemeFieldAlgebra k sY
  let := schemeFieldAlgebra k sZ
  let : Algebra Z.functionField Y.functionField := (dominantFunctionFieldMap g).toAlgebra
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  let : Algebra Z.functionField X.functionField := (dominantFunctionFieldMap (f ≫ g)).toAlgebra
  let : IsScalarTower k Z.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a => (dominantFunctionFieldMap_scalar k sY sZ g hg a).symm)
  let : IsScalarTower k Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a => (dominantFunctionFieldMap_scalar k sX sY f hf a).symm)
  let : IsScalarTower k Z.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (dominantFunctionFieldMap_scalar k sX sZ (f ≫ g) (by rw [Category.assoc,hg,hf]) a).symm)
  let : IsScalarTower Z.functionField Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a => (dominantFunctionFieldMap_comp_apply f g a))
  exact (LinearMap.congr_fun (topDifferentialMap_comp k Z.functionField Y.functionField
    X.functionField n) ω).symm
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma topDifferentialMap_self (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    (n : ℕ) : topDifferentialMap k A A n = LinearMap.id := by
  have hh : KaehlerDifferential.map k k A A = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    change KaehlerDifferential.map k k A A (KaehlerDifferential.D k A a) =
      KaehlerDifferential.D k A a
    simp only [KaehlerDifferential.map_D,Algebra.algebraMap_self_apply]
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply,LinearMap.id_apply,
    topDifferentialMap_ιMulti,hh,LinearMap.id_apply]
lemma topDifferentialMap_self_of_algebra_eq (k A : Type*) [CommRing k] [CommRing A]
    [Algebra k A] (n : ℕ) (ω : ⋀[A]^n Ω[A⁄k])
    (iAA : Algebra A A) (ht : @IsScalarTower k A A _ iAA.toSMul _)
    (hA : iAA = Algebra.id A) :
    @topDifferentialMap k A A _ _ _ _ _ iAA ht n ω = ω := by
  subst iAA
  exact LinearMap.congr_fun (topDifferentialMap_self k A n) ω
lemma rationalTopFormPullback_congr (k : CommRingCat)
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (sX : X ⟶ Spec k) (sY : Y ⟶ Spec k) (f g : X ⟶ Y)
    [hfDom : IsDominant f] [hgDom : IsDominant g] (hf : f ≫ sY = sX) (hg : g ≫ sY = sX)
    (h : f = g) (n : ℕ) :
    rationalTopFormPullback k sX sY f hf n = rationalTopFormPullback k sX sY g hg n := by
  subst g
  rfl
lemma rationalTopFormPullback_id (k : CommRingCat) {X : Scheme} [IsIntegral X]
    (sX : X ⟶ Spec k) (n : ℕ) (ω : rationalTopForms k sX n) :
    rationalTopFormPullback k sX sX (𝟙 X) (Category.id_comp sX) n ω = ω := by
  let := schemeFieldAlgebra k sX
  apply topDifferentialMap_self_of_algebra_eq k X.functionField n ω
  exact Algebra.algebra_ext _ _ dominantFunctionFieldMap_id_apply
lemma rationalTopFormPullback_isIso_injective (k : CommRingCat)
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (sX : X ⟶ Spec k) (sY : Y ⟶ Spec k) (f : X ⟶ Y) [IsIso f]
    (hf : f ≫ sY = sX) (n : ℕ) :
    Function.Injective (rationalTopFormPullback k sX sY f hf n) := by
  have hg : inv f ≫ sX = sY := by rw [← hf,← Category.assoc,IsIso.inv_hom_id,Category.id_comp]
  intro a b hab
  have h := congrArg (rationalTopFormPullback k sY sX (inv f) hg n) hab
  rw [← rationalTopFormPullback_comp,← rationalTopFormPullback_comp] at h
  simpa only [IsIso.inv_hom_id,rationalTopFormPullback_id] using h
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma CompatibleCanonicalData.symm {n : ℕ} {X Y : CanonicalModel n}
    {φ : X.scheme.PartialIso Y.scheme} {hφ : φ.IsOver X.structureMap Y.structureMap}
    (hc : CompatibleCanonicalData X Y φ hφ) :
    CompatibleCanonicalData Y X φ.symm hφ.symm := by
  dsimp only [CompatibleCanonicalData,Scheme.PartialIso.symm] at *
  apply rationalTopFormPullback_isIso_injective (.of ℂ)
    (φ.source.ι ≫ X.structureMap) (φ.target.ι ≫ Y.structureMap) φ.iso.hom hφ n
  change rationalTopFormPullback _ _ _ φ.iso.hom hφ n
      (rationalTopFormPullback _ _ _ φ.target.ι rfl n Y.form) =
    rationalTopFormPullback _ _ _ φ.iso.hom hφ n
      (rationalTopFormPullback _ _ _ (φ.iso.inv ≫ φ.source.ι) _ n X.form)
  rw [← rationalTopFormPullback_comp,← rationalTopFormPullback_comp]
  simpa only [← Category.assoc,Iso.hom_inv_id,Category.id_comp] using hc.symm
lemma CompatibleCanonicalData.restrictSource {n : ℕ} {X Y : CanonicalModel n}
    {φ : X.scheme.PartialIso Y.scheme} {hφ : φ.IsOver X.structureMap Y.structureMap}
    (hc : CompatibleCanonicalData X Y φ hφ)
    (U : X.scheme.Opens) (hU : Dense (U : Set X.scheme)) (hle : U ≤ φ.source) :
    CompatibleCanonicalData X Y (φ.restrictSource U hU hle) (hφ.restrictSource U hU hle) := by
  let : Nonempty U := hU.nonempty.to_subtype
  let : IsDominant U.ι := Opens.isDominant_ι hU
  let α := X.scheme.homOfLE hle
  let : IsDominant α := Opens.isDominant_homOfLE hU hle
  have ha : α ≫ (φ.source.ι ≫ X.structureMap) = U.ι ≫ X.structureMap := by
    dsimp [α]
    simp only [Scheme.homOfLE_ι_assoc]
  have hα : (Scheme.Opens.isoOfLE hle).inv ≫ (φ.source.ι ⁻¹ᵁ U).ι = α := by
    apply (cancel_mono φ.source.ι).mp
    dsimp [α]
    simp only [Category.assoc,Scheme.Opens.isoOfLE_inv_ι,Scheme.homOfLE_ι]
  have hw : (φ.restrictSource U hU hle).iso.hom ≫
      (φ.restrictSource U hU hle).target.ι = α ≫ φ.iso.hom ≫ φ.target.ι := by
    change (((Scheme.Opens.isoOfLE hle).inv ≫
      (Scheme.Hom.isoImage φ.iso.hom (φ.source.ι ⁻¹ᵁ U)).hom) ≫
      (Scheme.Hom.isoImage φ.target.ι (φ.iso.hom ''ᵁ φ.source.ι ⁻¹ᵁ U)).hom) ≫
      (φ.target.ι ''ᵁ φ.iso.hom ''ᵁ φ.source.ι ⁻¹ᵁ U).ι = _
    simp only [Category.assoc,Scheme.Hom.isoImage_hom_ι,
      Scheme.Hom.isoImage_hom_ι_assoc]
    rw [← Category.assoc,← Category.assoc,hα,Category.assoc]
  have hh := congrArg (rationalTopFormPullback (.of ℂ) (U.ι ≫ X.structureMap)
    (φ.source.ι ≫ X.structureMap) α ha n) hc
  rw [← rationalTopFormPullback_comp,← rationalTopFormPullback_comp] at hh
  unfold CompatibleCanonicalData
  change rationalTopFormPullback _ _ _ U.ι rfl n X.form =
    rationalTopFormPullback _ _ _ ((φ.restrictSource U hU hle).iso.hom ≫
      (φ.restrictSource U hU hle).target.ι) _ n Y.form
  have hr : ((φ.restrictSource U hU hle).iso.hom ≫
      (φ.restrictSource U hU hle).target.ι) ≫ Y.structureMap = U.ι ≫ X.structureMap := by
    have h := hφ.restrictSource U hU hle
    change (φ.restrictSource U hU hle).iso.hom ≫
      (φ.restrictSource U hU hle).target.ι ≫ Y.structureMap = U.ι ≫ X.structureMap at h
    exact (Category.assoc _ _ _).trans h
  have hdom : IsDominant ((φ.restrictSource U hU hle).iso.hom ≫
      (φ.restrictSource U hU hle).target.ι) := inferInstance
  have hdomg : IsDominant (α ≫ φ.iso.hom ≫ φ.target.ι) := inferInstance
  have hg : (α ≫ φ.iso.hom ≫ φ.target.ι) ≫ Y.structureMap = U.ι ≫ X.structureMap := by
    simpa only [Category.assoc,hφ] using ha
  have hw' := rationalTopFormPullback_congr (.of ℂ)
    (X := U.toScheme) (U.ι ≫ X.structureMap)
    Y.structureMap ((φ.restrictSource U hU hle).iso.hom ≫
      (φ.restrictSource U hU hle).target.ι) (α ≫ φ.iso.hom ≫ φ.target.ι)
    (hfDom := hdom) (hgDom := hdomg) hr hg hw n
  have hx : rationalTopFormPullback (.of ℂ) (U.ι ≫ X.structureMap) X.structureMap
      U.ι rfl n X.form = rationalTopFormPullback (.of ℂ) (U.ι ≫ X.structureMap)
      Y.structureMap (α ≫ φ.iso.hom ≫ φ.target.ι) hg n Y.form := by
    simpa only [α,Scheme.homOfLE_ι] using hh
  exact Eq.trans hx (congrFun hw' Y.form).symm
lemma CompatibleCanonicalData.restrictTarget {n : ℕ} {X Y : CanonicalModel n}
    {φ : X.scheme.PartialIso Y.scheme} {hφ : φ.IsOver X.structureMap Y.structureMap}
    (hc : CompatibleCanonicalData X Y φ hφ)
    (U : Y.scheme.Opens) (hU : Dense (U : Set Y.scheme)) (hle : U ≤ φ.target) :
    CompatibleCanonicalData X Y (φ.restrictTarget U hU hle) (hφ.restrictTarget U hU hle) :=
  (hc.symm.restrictSource U hU hle).symm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma NoExtractionOn.refl (X : Scheme) : NoExtractionOn (.refl X) := by
  intro p
  trivial
lemma NoExtractionOn.trans {X Y Z : Scheme} {φ : X.PartialIso Y} {ψ : Y.PartialIso Z}
    (hφ : NoExtractionOn φ) (hψ : NoExtractionOn ψ) : NoExtractionOn (φ.trans ψ) := by
  intro p
  let z : ψ.target.toScheme := ⟨p.1,hψ p⟩
  let y : ψ.source.toScheme := ψ.iso.inv z
  have hy : Order.coheight (ψ.source.ι y) = 1 := by
    calc
      _ = Order.coheight y := coheight_eq_of_isOpenImmersion ψ.source.ι
      _ = Order.coheight z := coheight_eq_of_isOpenImmersion ψ.iso.inv
      _ = Order.coheight p.1 := (coheight_eq_of_isOpenImmersion (x := z) ψ.target.ι).symm
      _ = 1 := p.2
  have hymem : ψ.source.ι y ∈ φ.target := hφ ⟨ψ.source.ι y,hy⟩
  rw [Scheme.PartialIso.trans_target]
  change p.1 ∈ ψ.target.ι '' (ψ.iso.hom '' (ψ.source.ι ⁻¹' (φ.target ⊓ ψ.source : Y.Opens)))
  refine ⟨z,⟨y,⟨hymem,y.2⟩,?_⟩,rfl⟩
  change ψ.iso.hom (ψ.iso.inv z) = z
  exact congrArg (fun h : ψ.target.toScheme ⟶ ψ.target.toScheme => h z) ψ.iso.inv_hom_id
lemma CanonicalMMPChain.noExtraction {n : ℕ} {X Y : CanonicalModel n}
    {φ : X.scheme.PartialIso Y.scheme} (h : CanonicalMMPChain X Y φ) : NoExtractionOn φ := by
  induction h with
  | refl X => exact NoExtractionOn.refl X.scheme
  | step hs _ ih => exact hs.2.2.2.2.1.trans ih
lemma CanonicalMMPChain.isOver {n : ℕ} {X Y : CanonicalModel n}
    {φ : X.scheme.PartialIso Y.scheme} (h : CanonicalMMPChain X Y φ) :
    φ.IsOver X.structureMap Y.structureMap := by
  induction h with
  | refl X => exact Category.id_comp _
  | step hs _ ih => exact hs.2.2.2.2.2.choose.trans ih
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma CompatibleCanonicalData.refl {n : ℕ} (X : CanonicalModel n) :
    CompatibleCanonicalData X X (.refl X.scheme) (Category.id_comp _) := by
  dsimp only [CompatibleCanonicalData,Scheme.PartialIso.refl,Iso.refl_hom]
  simp only [Category.id_comp]
lemma CompatibleCanonicalData.trans' {n : ℕ} {X Y Z : CanonicalModel n}
    {φ : X.scheme.PartialIso Y.scheme} {ψ : Y.scheme.PartialIso Z.scheme}
    {hφ : φ.IsOver X.structureMap Y.structureMap}
    {hψ : ψ.IsOver Y.structureMap Z.structureMap}
    (hcφ : CompatibleCanonicalData X Y φ hφ)
    (hcψ : CompatibleCanonicalData Y Z ψ hψ) (e : φ.target = ψ.source) :
    CompatibleCanonicalData X Z (φ.trans' ψ e) (hφ.trans' hψ) := by
  let α := φ.iso.hom ≫ (Y.scheme.isoOfEq e).hom
  have hα : α ≫ ψ.source.ι = φ.iso.hom ≫ φ.target.ι := by
    dsimp only [α]
    rw [Category.assoc,Scheme.isoOfEq_hom_ι]
  have ha : α ≫ (ψ.source.ι ≫ Y.structureMap) = φ.source.ι ≫ X.structureMap := by
    rw [← Category.assoc,hα,Category.assoc]
    exact hφ
  have hb : α ≫ (ψ.iso.hom ≫ ψ.target.ι) =
      (φ.trans' ψ e).iso.hom ≫ (φ.trans' ψ e).target.ι := by
    dsimp only [α,Scheme.PartialIso.trans',Iso.trans_hom]
    simp only [Category.assoc]
  have hh := congrArg (rationalTopFormPullback (.of ℂ) (φ.source.ι ≫ X.structureMap)
    (ψ.source.ι ≫ Y.structureMap) α ha n) hcψ
  rw [← rationalTopFormPullback_comp,← rationalTopFormPullback_comp] at hh
  have he₁ := rationalTopFormPullback_congr (.of ℂ) (φ.source.ι ≫ X.structureMap)
    Y.structureMap (α ≫ ψ.source.ι) (φ.iso.hom ≫ φ.target.ι)
    (by rw [Category.assoc]; exact ha) (by rw [Category.assoc]; exact hφ) hα n
  have hdom : IsDominant ((φ.trans' ψ e).iso.hom ≫ (φ.trans' ψ e).target.ι) := inferInstance
  have hr : ((φ.trans' ψ e).iso.hom ≫ (φ.trans' ψ e).target.ι) ≫ Z.structureMap =
      φ.source.ι ≫ X.structureMap := by
    have h := hφ.trans' (e := e) hψ
    change (φ.trans' ψ e).iso.hom ≫ (φ.trans' ψ e).target.ι ≫ Z.structureMap =
      φ.source.ι ≫ X.structureMap at h
    exact (Category.assoc _ _ _).trans h
  have hdomg : IsDominant (α ≫ (ψ.iso.hom ≫ ψ.target.ι)) := inferInstance
  have hg : (α ≫ (ψ.iso.hom ≫ ψ.target.ι)) ≫ Z.structureMap =
      φ.source.ι ≫ X.structureMap := by
    simpa only [Category.assoc,hψ] using ha
  have he₂ := rationalTopFormPullback_congr (.of ℂ)
    (X := φ.source.toScheme) (φ.source.ι ≫ X.structureMap)
    Z.structureMap (α ≫ (ψ.iso.hom ≫ ψ.target.ι))
    ((φ.trans' ψ e).iso.hom ≫ (φ.trans' ψ e).target.ι)
    (hfDom := hdomg) (hgDom := hdom) hg hr hb n
  exact Eq.trans hcφ (Eq.trans (congrFun he₁ Y.form).symm
    (Eq.trans hh (congrFun he₂ Z.form)))
lemma CompatibleCanonicalData.trans {n : ℕ} {X Y Z : CanonicalModel n}
    {φ : X.scheme.PartialIso Y.scheme} {ψ : Y.scheme.PartialIso Z.scheme}
    {hφ : φ.IsOver X.structureMap Y.structureMap}
    {hψ : ψ.IsOver Y.structureMap Z.structureMap}
    (hcφ : CompatibleCanonicalData X Y φ hφ)
    (hcψ : CompatibleCanonicalData Y Z ψ hψ) :
    CompatibleCanonicalData X Z (φ.trans ψ) (hφ.trans hψ) := by
  exact (hcφ.restrictTarget _ _ _).trans' (hcψ.restrictSource _ _ _) rfl
lemma CanonicalMMPChain.compatible {n : ℕ} {X Y : CanonicalModel n}
    {φ : X.scheme.PartialIso Y.scheme} (h : CanonicalMMPChain X Y φ) :
    CompatibleCanonicalData X Y φ h.isOver := by
  induction h with
  | refl X => exact CompatibleCanonicalData.refl X
  | step hs _ ih => exact hs.2.2.2.2.2.choose_spec.1.trans ih
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
section RationalPullbackUniqueness
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

lemma IsCartierPullback.nsmul {f : X ⟶ Y} [IsDominant f]
    {D : WeilDivisor Y} {P : WeilDivisor X} (hP : IsCartierPullback f D P) (m : ℕ) :
    IsCartierPullback f (m • D) (m • P) := by
  induction m with
  | zero => simpa using isCartierPullback_zero f
  | succ m hm => simpa only [succ_nsmul] using hm.add hP

lemma IsQCartierPullback.eq_integral [StalkwiseNormal Y]
    {f : X ⟶ Y} [IsDominant f] {D : WeilDivisor Y} {P : WeilDivisor X}
    (hP : IsCartierPullback f D P) {Q : QWeilDivisor X}
    (hQ : IsQCartierPullback f (rationalWeilDivisor D) Q) :
    Q = rationalWeilDivisor P := by
  obtain ⟨m, hm, A, B, _, hA, hB, hAB⟩ := hQ
  have heA : A = m • D := by
    ext p
    have h := DFunLike.congr_fun hA p
    change (m : ℚ) * (D p : ℚ) = (A p : ℚ) at h
    change A p = (m : ℤ) * D p
    exact_mod_cast h.symm
  rw [heA] at hAB
  have heB := hAB.unique (hP.nsmul m)
  ext p
  have h := DFunLike.congr_fun hB p
  rw [heB] at h
  change (m : ℚ) * Q p = ((m : ℤ) * P p : ℤ) at h
  push_cast at h
  change Q p = (P p : ℚ)
  exact (mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))) h
end RationalPullbackUniqueness
end NumericalDimensionOne

end OAI
