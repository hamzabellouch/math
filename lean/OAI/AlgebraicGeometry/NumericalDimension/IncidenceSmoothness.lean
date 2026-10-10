import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.SectionCoordinates

namespace OAI

/-! Incidence Smoothness. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace NumericalDimensionOne
noncomputable section
variable (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    {N : ℕ} (D : WeilDivisor X) (s : Fin (N+1) → X.functionField)

structure DivisorAffineAtlas where
  index : Type
  finite : Fintype index
  chart : index → DivisorProjectiveChart X D s
  affine : ∀ i, IsAffineOpen (chart i).domain
  covers : ∀ x : X, ∃ i, x ∈ (chart i).domain
attribute [instance] DivisorAffineAtlas.finite
variable {X D s}
namespace DivisorAffineAtlas
variable (A : DivisorAffineAtlas X D s)
def cover : X.OpenCover where
  I₀ := A.index
  X i := (A.chart i).domain.toScheme
  f i := (A.chart i).domain.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_,inferInstance⟩
    obtain ⟨i,hi⟩ := A.covers x
    exact ⟨i,⟨⟨x,hi⟩,rfl⟩⟩
instance : Fintype A.cover.I₀ := A.finite
instance (i : A.cover.I₀) : IsAffine (A.cover.X i) := A.affine i
def coordinate (i : A.index) (j : Fin (N+1)) : Γ(A.cover.X i,⊤) :=
  (A.chart i).domain.topIso.inv ((A.chart i).normalized j)
end DivisorAffineAtlas

theorem exists_divisorAffineAtlas [StalkwiseNormal X] [CompactSpace X]
    (hD : IsCartierDivisor D) (hs : ∀ i, s i ≠ 0 ∧ IsDivisorSection D (s i))
    (hcov : ∀ x : X, ∃ i, x ∈ sectionNonvanishing D (s i)) :
    Nonempty (DivisorAffineAtlas X D s) := by
  classical
  choose C hC hA using fun x => exists_affine_divisorProjectiveChart hD hs x (hcov x)
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => ((C x).domain : Set X))
    (fun x => (C x).domain.isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x,hC x⟩)
  let e := (Fintype.equivFin S).symm
  refine ⟨⟨Fin (Fintype.card S),inferInstance,fun i => C (e i).1,fun i => hA (e i).1,?_⟩⟩
  intro x
  obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ x))
  exact ⟨e.symm ⟨y,hy⟩,by simpa using hxy⟩
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace NumericalDimensionOne
noncomputable section
universe u
lemma idealSheaf_comap_inf_open {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (I J : Y.IdealSheafData) :
    (I ⊓ J).comap f = I.comap f ⊓ J.comap f := by
  ext U : 2
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_inf,Pi.inf_apply,Ideal.comap_inf]
lemma idealSheaf_comap_ker_open {X Y V : Scheme.{u}}
    (f : X ⟶ Y) (j : V ⟶ Y) [IsOpenImmersion j] [QuasiCompact f] :
    f.ker.comap j = (pullback.fst j f).ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f (pullback.fst j f)
      (pullback.snd j f) j (IsPullback.of_hasPullback j f)]
lemma idealSheaf_comap_map_open {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] [QuasiCompact f] (I : X.IdealSheafData) :
    (I.map f).comap f = I := by
  rw [Scheme.IdealSheafData.map,idealSheaf_comap_ker_open]
  have h : IsPullback I.subschemeι (𝟙 _) f (I.subschemeι ≫ f) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  rw [← Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom]
  simp

theorem idealSheaf_open_baseChange
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ V)
    (i : U ⟶ X) (j : V ⟶ Y) [IsOpenImmersion j] [QuasiCompact f]
    (h : IsPullback g i j f) (I : X.IdealSheafData) :
    (I.map f).comap j = (I.comap i).map g
 := by
  have : IsOpenImmersion i := MorphismProperty.of_isPullback h inferInstance
  have : QuasiCompact g := MorphismProperty.of_isPullback h.flip inferInstance
  rw [Scheme.IdealSheafData.map,idealSheaf_comap_ker_open,
    Scheme.IdealSheafData.map,
    ← Scheme.Hom.ker_comp_of_isIso (I.comapIso i).inv]
  simp only [Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc]
  have H := (IsPullback.of_hasPullback i I.subschemeι).paste_horiz h
  rw [← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom]
  simp
lemma idealSheaf_comap_iInf_open {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {ι : Type u} [Finite ι] (I : ι → Y.IdealSheafData) :
    (⨅ i, I i).comap f = ⨅ i, (I i).comap f := by
  classical
  let := Fintype.ofFinite ι
  let e : InfTopHom Y.IdealSheafData X.IdealSheafData :=
    ⟨⟨fun I => I.comap f,idealSheaf_comap_inf_open f⟩,
      Scheme.IdealSheafData.comap_top f⟩
  change e (⨅ i, I i) = ⨅ i, e (I i)
  rw [← Finset.inf_univ_eq_iInf, map_finset_inf, Finset.inf_univ_eq_iInf]
  rfl

theorem idealSheaf_finite_glue {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (I : ∀ i, (U i).toScheme.IdealSheafData)
    (h : ∀ i j, (I i).comap (X.homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)) =
      (I j).comap (X.homOfLE (show U i ⊓ U j ≤ U j from inf_le_right))) :
    ∃ J : X.IdealSheafData, ∀ i, J.comap (U i).ι = I i
 := by
  refine ⟨⨅ i, (I i).map (U i).ι,?_⟩
  intro i
  have hqc (j : ι) : QuasiCompact (U j).ι := inferInstance
  rw [idealSheaf_comap_iInf_open]
  apply le_antisymm
  · exact (iInf_le _ i).trans_eq (idealSheaf_comap_map_open (U i).ι (I i))
  · apply le_iInf
    intro j
    rw [idealSheaf_open_baseChange (U j).ι (X.homOfLE inf_le_left)
      (X.homOfLE inf_le_right) (U i).ι (isPullback_opens_inf (U i) (U j)),← h]
    exact Scheme.IdealSheafData.le_map_comap _ _
lemma idealSheaf_comap_ofIdealTop_open {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (I : Ideal Γ(Y,⊤)) :
    (Scheme.IdealSheafData.ofIdealTop I).comap f =
      Scheme.IdealSheafData.ofIdealTop (I.map f.appTop.hom) := by
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal,Ideal.map_map]
  have he : (X.presheaf.map (homOfLE le_top).op).hom.comp f.appTop.hom =
      (f.appIso U).hom.hom.comp (Y.presheaf.map (homOfLE le_top).op).hom := by
    change (f.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom =
      (Y.presheaf.map (homOfLE le_top).op ≫ (f.appIso U).hom).hom
    congr 1
    simp only [Scheme.Hom.appIso_hom',Scheme.Hom.app_eq_appLE,
      Scheme.Hom.map_appLE]
    exact f.appLE_map (U := ⊤) (V := ⊤) (V' := U.1) le_rfl (homOfLE le_top).op
  rw [he,← Ideal.map_map]
  exact Ideal.comap_symm (f.appIso U).commRingCatIsoToRingEquiv

theorem idealSheaf_finite_openImmersion_glue
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (V : ι → Scheme.{u})
    (f : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (f i)] [∀ i, QuasiCompact (f i)]
    (I : ∀ i, (V i).IdealSheafData)
    (h : ∀ i j, (I i).comap (pullback.fst (f i) (f j)) =
      (I j).comap (pullback.snd (f i) (f j))) :
    ∃ J : X.IdealSheafData, ∀ i, J.comap (f i) = I i
 := by
  refine ⟨⨅ i, (I i).map (f i),?_⟩
  intro i
  rw [idealSheaf_comap_iInf_open]
  apply le_antisymm
  · exact (iInf_le _ i).trans_eq (idealSheaf_comap_map_open (f i) (I i))
  · apply le_iInf
    intro j
    rw [idealSheaf_open_baseChange (f j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) (f i) (IsPullback.of_hasPullback _ _),← h]
    exact Scheme.IdealSheafData.le_map_comap _ _
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace NumericalDimensionOne
noncomputable section
universe u

def universalLinearSection {n : Type u} [Fintype n] {X : Scheme.{u}}
    (r : n → Γ(X,⊤)) : Γ(𝔸(n;X),⊤) :=
  ∑ j, (𝔸(n;X) ↘ X).appTop (r j) * AffineSpace.coord X j
lemma universalLinearSection_span_eq {n : Type u} [Fintype n]
    {W X Y : Scheme.{u}} (a : W ⟶ 𝔸(n;X)) (b : W ⟶ 𝔸(n;Y))
    (r : n → Γ(X,⊤)) (s : n → Γ(Y,⊤)) (e : Γ(W,⊤)ˣ)
    (hc : ∀ l, a.appTop (AffineSpace.coord X l) = b.appTop (AffineSpace.coord Y l))
    (hr : ∀ l, (a ≫ 𝔸(n;X) ↘ X).appTop (r l) =
      e * (b ≫ 𝔸(n;Y) ↘ Y).appTop (s l)) :
    Ideal.span {a.appTop (universalLinearSection r)} =
      Ideal.span {b.appTop (universalLinearSection s)} := by
  have h : a.appTop (universalLinearSection r) = e * b.appTop (universalLinearSection s) := by
    simp only [universalLinearSection,map_sum,map_mul,← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [hr,hc,mul_assoc]
  rw [h,Ideal.span_singleton_mul_left_unit e.isUnit]

theorem universal_incidence_exists
    {n a : Type u} [Fintype n] [Finite a] {X : Scheme.{u}}
    (V : a → Scheme.{u}) (f : ∀ i, V i ⟶ X)
    [∀ i, IsOpenImmersion (f i)] [∀ i, QuasiCompact (f i)]
    (r : ∀ i, n → Γ(V i,⊤))
    (htrans : ∀ i j, ∃ e : Γ(pullback (f i) (f j),⊤)ˣ,
      ∀ l, (pullback.fst (f i) (f j)).appTop (r i l) =
        e * (pullback.snd (f i) (f j)).appTop (r j l)) :
    ∃ J : 𝔸(n;X).IdealSheafData, ∀ i,
      J.comap (AffineSpace.map n (f i)) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (r i)}) := by
  have ho (i : a) : IsOpenImmersion (AffineSpace.map n (f i)) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map (n := n) (f i)).flip inferInstance
  have hq (i : a) : QuasiCompact (AffineSpace.map n (f i)) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map (n := n) (f i)).flip inferInstance
  apply idealSheaf_finite_openImmersion_glue (fun i => 𝔸(n;V i))
    (fun i => AffineSpace.map n (f i))
    (fun i => Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (r i)}))
  intro i j
  obtain ⟨e,he⟩ := htrans i j
  let α := pullback.fst (AffineSpace.map n (f i)) (AffineSpace.map n (f j))
  let β := pullback.snd (AffineSpace.map n (f i)) (AffineSpace.map n (f j))
  have hab : (α ≫ 𝔸(n;V i) ↘ V i) ≫ f i = (β ≫ 𝔸(n;V j) ↘ V j) ≫ f j := by
    simpa only [Category.assoc,AffineSpace.map_over] using
      congrArg (fun z => z ≫ 𝔸(n;X) ↘ X)
        (pullback.condition (f := AffineSpace.map n (f i)) (g := AffineSpace.map n (f j)))
  let g := pullback.lift (α ≫ 𝔸(n;V i) ↘ V i) (β ≫ 𝔸(n;V j) ↘ V j) hab
  rw [idealSheaf_comap_ofIdealTop_open,idealSheaf_comap_ofIdealTop_open]
  simp only [Ideal.map_span,Set.image_singleton]
  congr 1
  apply universalLinearSection_span_eq α β (r i) (r j) (Units.map g.appTop.hom e)
  · intro l
    have h := congrArg (fun z => z.appTop (AffineSpace.coord X l))
      (pullback.condition (f := AffineSpace.map n (f i)) (g := AffineSpace.map n (f j)))
    simpa only [Scheme.Hom.comp_appTop,CommRingCat.comp_apply,AffineSpace.map_appTop_coord]
      using h
  · intro l
    have h := congrArg g.appTop (he l)
    simpa only [map_mul,← CommRingCat.comp_apply,← Scheme.Hom.comp_appTop,
      g,pullback.lift_fst,pullback.lift_snd,Units.coe_map] using! h
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace NumericalDimensionOne
noncomputable section
universe u v w

def eliminationPolynomial {R : Type v} [CommRing R] {ι : Type w}
    (G : MvPolynomial ι R) : MvPolynomial (Option ι) R :=
  MvPolynomial.X none + MvPolynomial.rename some G
lemma optionEquivLeft_rename_some {R ι : Type*} [CommRing R]
    (G : MvPolynomial ι R) : MvPolynomial.optionEquivLeft R ι (MvPolynomial.rename some G) =
      Polynomial.C G := by
  have h : (MvPolynomial.optionEquivLeft R ι).toAlgHom.comp (MvPolynomial.rename some) =
      Polynomial.CAlgHom := by
    ext i
    simp
  exact AlgHom.congr_fun h G

noncomputable def eliminationAlgEquiv {R ι : Type*} [CommRing R]
    (G : MvPolynomial ι R) :
    (MvPolynomial (Option ι) R ⧸ Ideal.span {eliminationPolynomial G}) ≃ₐ[R]
      MvPolynomial ι R :=
  (Ideal.quotientEquivAlg _ _ (MvPolynomial.optionEquivLeft R ι) (by
    rw [Ideal.map_span,Set.image_singleton]
    simp [eliminationPolynomial,optionEquivLeft_rename_some,sub_neg_eq_add])).trans
    ((Polynomial.quotientSpanXSubCAlgEquiv (-G)).restrictScalars R)

theorem affine_hyperplane_equation_smooth
    (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    [Algebra.Smooth k R] {ι : Type w} [Finite ι] (G : MvPolynomial ι R) :
    Algebra.Smooth k (MvPolynomial (Option ι) R ⧸ Ideal.span {eliminationPolynomial G})
 := by
  have : Algebra.Smooth R (MvPolynomial ι R) := ⟨inferInstance,inferInstance⟩
  have : Algebra.Smooth k (MvPolynomial ι R) := .comp k R _
  exact Algebra.Smooth.of_equiv ((eliminationAlgEquiv G).symm.restrictScalars k)

def universalLinearPolynomial {R : Type v} [CommRing R] {ι : Type w} [Fintype ι]
    (r : ι → R) : MvPolynomial ι R := ∑ i, MvPolynomial.C (r i) * MvPolynomial.X i
lemma rename_universal_linear {R : Type v} [CommRing R] {ι : Type w} [Fintype ι] [DecidableEq ι]
    (r : ι → R) (i : ι) (hi : r i = 1) :
    MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe i).symm (universalLinearPolynomial r) =
      eliminationPolynomial (∑ j : {j : ι // j ≠ i},
        MvPolynomial.C (r j.1) * MvPolynomial.X j) := by
  classical
  rw [universalLinearPolynomial]
  simp only [map_sum,map_mul,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_C,
    MvPolynomial.rename_X]
  rw [← (Equiv.optionSubtypeNe i).sum_comp]
  simp [Equiv.optionSubtypeNe,hi,eliminationPolynomial,map_sum,map_mul]
noncomputable def universalLinearQuotientEquiv {R : Type v} [CommRing R]
    {ι : Type w} [Fintype ι] (r : ι → R) (i : ι) (hi : r i = 1) :
    (MvPolynomial ι R ⧸ Ideal.span {universalLinearPolynomial r}) ≃ₐ[R]
      MvPolynomial {j : ι // j ≠ i} R := by
  classical
  let G : MvPolynomial {j : ι // j ≠ i} R :=
    ∑ j : {j : ι // j ≠ i}, MvPolynomial.C (r j.1) * MvPolynomial.X j
  refine (Ideal.quotientEquivAlg _ _
    (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe i).symm) ?_).trans
      (eliminationAlgEquiv G)
  rw [Ideal.map_span,Set.image_singleton]
  exact congrArg (fun x => Ideal.span {x}) (rename_universal_linear r i hi).symm

theorem universal_linear_equation_smooth
    (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    [Algebra.Smooth k R] {ι : Type w} [Fintype ι] (r : ι → R) (i : ι)
    (hi : r i = 1) : Algebra.Smooth k
      (MvPolynomial ι R ⧸ Ideal.span {universalLinearPolynomial r}) := by
  have : Algebra.Smooth R (MvPolynomial {j : ι // j ≠ i} R) :=
    ⟨inferInstance,inferInstance⟩
  have : Algebra.Smooth k (MvPolynomial {j : ι // j ≠ i} R) := .comp k R _
  exact Algebra.Smooth.of_equiv ((universalLinearQuotientEquiv r i hi).symm.restrictScalars k)
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace NumericalDimensionOne
noncomputable section
universe u

theorem affine_subscheme_smooth_of_quotient
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (s : X ⟶ Y)
    (J : Ideal Γ(X,⊤))
    (h : ((Ideal.Quotient.mk J).comp s.appTop.hom).Smooth) :
    Smooth ((Scheme.IdealSheafData.ofIdealTop J).subschemeι ≫ s) := by
  let I := Scheme.IdealSheafData.ofIdealTop J
  let U : X.affineOpens := ⟨⊤,isAffineOpen_top X⟩
  have hh : ((Ideal.Quotient.mk (I.ideal U)).comp s.appTop.hom).Smooth := by
    have hI : I.ideal U = J := by simp [I,U,Scheme.IdealSheafData.ofIdealTop_ideal]
    rw [hI]
    exact h
  have he : Function.Bijective (I.subschemeObjIso U).inv.hom :=
    (I.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.bijective
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  apply (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mpr
  change RingHom.Smooth (I.subschemeι.appTop.hom.comp s.appTop.hom)
  have happ := I.subschemeι_app U
  change I.subschemeι.appTop = _ at happ
  rw [happ]
  erw [CommRingCat.hom_comp,RingHom.comp_assoc]
  exact hh.comp (RingHom.Smooth.of_bijective he)
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace NumericalDimensionOne
noncomputable section
universe u v w
lemma linear_equation_ringSmooth_under_equiv
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {n : Type w} [Fintype n] (e : MvPolynomial n R ≃+* S) (φ : R →+* S)
    (he : ∀ x, e (MvPolynomial.C x) = φ x)
    (r : n → R) (i : n) (hi : r i = 1) :
    ((Ideal.Quotient.mk (Ideal.span {e (universalLinearPolynomial r)})).comp φ).Smooth := by
  let J := Ideal.span {universalLinearPolynomial r}
  let H := Ideal.span {e (universalLinearPolynomial r)}
  let q := Ideal.quotientEquiv J H e (by dsimp [J, H]; rw [Ideal.map_span, Set.image_singleton]; rfl)
  have hs : Algebra.Smooth R (MvPolynomial n R ⧸ J) :=
    universal_linear_equation_smooth R R r i hi
  have hp : ((Ideal.Quotient.mk J).comp MvPolynomial.C).Smooth := by
    change (algebraMap R (MvPolynomial n R ⧸ J)).Smooth
    exact RingHom.smooth_algebraMap.mpr hs
  have hq : q.toRingHom.Smooth := RingHom.Smooth.of_bijective q.bijective
  convert hp.comp hq using 1
  ext x
  change (Ideal.Quotient.mk H) (φ x) = q ((Ideal.Quotient.mk J) (MvPolynomial.C x))
  rw [Ideal.quotientEquiv_mk,he]
lemma affineSpace_global_coordinates {n : Type u} {X : Scheme.{u}} [IsAffine X] :
    ∃ e : MvPolynomial n Γ(X,⊤) ≃+* Γ(𝔸(n;X),⊤),
      (∀ x, e (MvPolynomial.C x) = (𝔸(n;X) ↘ X).appTop x) ∧
      (∀ j, e (MvPolynomial.X j) = AffineSpace.coord X j) := by
  let e := (AffineSpace.isoOfIsAffine n X)
  let er : MvPolynomial n Γ(X,⊤) ≃+* Γ(𝔸(n;X),⊤) :=
    ((Scheme.ΓSpecIso (.of (MvPolynomial n Γ(X,⊤)))).symm ≪≫
    Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv
  have h (p : MvPolynomial n Γ(X,⊤)) :
      er p = MvPolynomial.eval₂Hom (𝔸(n;X) ↘ X).appTop.hom (AffineSpace.coord X) p := by
    change (((Scheme.ΓSpecIso _).inv ≫ e.hom.appTop).hom p) = _
    simp only [e,AffineSpace.isoOfIsAffine_hom_appTop,Iso.inv_hom_id_assoc]
    rfl
  refine ⟨er,?_,?_⟩
  · intro x
    rw [h,MvPolynomial.eval₂Hom_C]
  · intro j
    simp [h]

end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace NumericalDimensionOne
noncomputable section
universe u

theorem universal_incidence_chart_smooth
    {n : Type u} [Fintype n] {X : Scheme.{u}} [IsAffine X]
    (r : n → Γ(X,⊤)) (i : n) (hi : r i = 1) :
    Smooth ((Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {universalLinearSection r})).subschemeι ≫ 𝔸(n;X) ↘ X) := by
  obtain ⟨e,hC,hX⟩ := affineSpace_global_coordinates (n := n) (X := X)
  apply affine_subscheme_smooth_of_quotient
  have hF : e (universalLinearPolynomial r) = universalLinearSection r := by
    simp only [universalLinearPolynomial,universalLinearSection,map_sum,map_mul,hC,hX]
  have H := linear_equation_ringSmooth_under_equiv e (𝔸(n;X) ↘ X).appTop.hom hC r i hi
  rw [hF] at H
  exact H
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace NumericalDimensionOne
noncomputable section
universe u

theorem universal_incidence_smooth_over
    {n : Type u} [Fintype n] {X : Scheme.{u}} (V : X.OpenCover)
    [∀ i, IsAffine (V.X i)] (r : ∀ i, n → Γ(V.X i,⊤))
    (hn : ∀ i, ∃ j, r i j = 1) (J : 𝔸(n;X).IdealSheafData)
    (hJ : ∀ i, J.comap (AffineSpace.map n (V.f i)) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (r i)})) :
    Smooth (J.subschemeι ≫ 𝔸(n;X) ↘ X) := by
  have : IsZariskiLocalAtTarget @Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth.{u})
  refine IsZariskiLocalAtTarget.of_openCover (P := @Smooth.{u}) V ?_
  intro i
  let a := AffineSpace.map n (V.f i)
  have hs : Smooth ((J.comap a).subschemeι ≫ 𝔸(n;V.X i) ↘ V.X i) := by
    rw [hJ i]
    obtain ⟨j,hj⟩ := hn i
    exact universal_incidence_chart_smooth (r i) j hj
  have hq : Smooth (pullback.fst a J.subschemeι ≫ 𝔸(n;V.X i) ↘ V.X i) := by
    rw [← J.comapIso_inv_subschemeι a,Category.assoc]
    infer_instance
  have hp := (IsPullback.of_hasPullback a J.subschemeι).flip.paste_vert
    (AffineSpace.isPullback_map (n := n) (V.f i))
  let e := hp.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)
  have he : e.hom ≫ pullback.snd (J.subschemeι ≫ 𝔸(n;X) ↘ X) (V.f i) =
      pullback.fst a J.subschemeι ≫ 𝔸(n;V.X i) ↘ V.X i :=
    hp.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback _ _)
  change Smooth (pullback.snd _ _)
  have : Smooth (e.hom ≫ pullback.snd (J.subschemeι ≫ 𝔸(n;X) ↘ X) (V.f i)) :=
    he.symm ▸ hq
  have : Smooth (e.inv ≫ e.hom ≫ pullback.snd (J.subschemeι ≫ 𝔸(n;X) ↘ X) (V.f i)) :=
    inferInstance
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

namespace NumericalDimensionOne

theorem formallySmooth_over_perfect_subfield
    (k K A : Type*) [Field k] [Field K] [CommRing A] [IsLocalRing A]
    [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
    [PerfectField K] [Algebra.EssFiniteType k K] [Algebra.EssFiniteType K A]
    [Algebra.FormallySmooth k A] : Algebra.FormallySmooth K A := by
  let κ := ResidueField A
  let f := KaehlerDifferential.mapBaseChange k K A
  let g := KaehlerDifferential.map k K A A
  have : Algebra.EssFiniteType k A := .comp k K A
  have : Module.Free A Ω[A⁄k] := Module.free_of_flat_of_isLocalRing
  have hfκ : Function.Injective (f.lTensor κ) := by
    have hfield : Function.Injective (KaehlerDifferential.mapBaseChange k K κ) := by
      have : Algebra.EssFiniteType K κ := .comp K A κ
      have : Algebra.FormallySmooth K κ := inferInstance
      rw [← LinearMap.ker_eq_bot, (Algebra.H1Cotangent.exact_δ_mapBaseChange k K κ).linearMap_ker_eq]
      exact LinearMap.range_eq_bot.mpr (Subsingleton.elim _ _)
    let c := AlgebraTensorModule.cancelBaseChange K A κ κ Ω[K⁄k]
    let d := KaehlerDifferential.mapBaseChange k A κ
    have hc : d.restrictScalars A ∘ₗ (f.lTensor κ) =
        (KaehlerDifferential.mapBaseChange k K κ).restrictScalars A ∘ₗ
          c.toLinearMap.restrictScalars A := by
      ext x y
      simp [d,f,c,AlgebraTensorModule.cancelBaseChange, ← IsScalarTower.algebraMap_apply]
    intro x y h
    apply c.injective
    apply hfield
    change ((KaehlerDifferential.mapBaseChange k K κ).restrictScalars A ∘ₗ c.toLinearMap.restrictScalars A) x =
      ((KaehlerDifferential.mapBaseChange k K κ).restrictScalars A ∘ₗ c.toLinearMap.restrictScalars A) y
    rw [← hc]
    exact congrArg d h
  have hf : Function.Injective f := by
    obtain ⟨r,hr⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr hfκ
    exact Function.HasLeftInverse.injective ⟨r,LinearMap.congr_fun hr⟩
  have hfree : Module.Free A Ω[A⁄K] :=
    Module.free_of_lTensor_residueField_injective f g
      (KaehlerDifferential.map_surjective k K A)
      (KaehlerDifferential.exact_mapBaseChange_map k K A) hfκ
  refine ⟨inferInstance,?_⟩
  apply (subsingleton_iff_forall_eq (0 : Algebra.H1Cotangent K A)).mpr
  intro x
  have hδ : Algebra.H1Cotangent.δ k K A x = 0 := by
    apply hf
    rw [map_zero]
    exact (Algebra.H1Cotangent.exact_δ_mapBaseChange k K A).apply_apply_eq_zero x
  obtain ⟨y,hy⟩ := (Algebra.H1Cotangent.exact_map_δ k K A x).mp hδ
  rw [← hy,Subsingleton.elim y 0,map_zero]

end NumericalDimensionOne

end OAI
