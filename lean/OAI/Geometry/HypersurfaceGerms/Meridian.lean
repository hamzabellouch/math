import Mathlib
import OAI.Geometry.HypersurfaceGerms.RootPages

namespace OAI

/-! Meridian sweeps, split section pairs and their homology maps. -/

namespace AmbientMultiplicity.InnerCircleSection
noncomputable section
open InnerGeometry CategoryTheory Topology
variable {G : Type} [TopologicalSpace G] (R : G → ℂ)

 
def collapseProjection : C(CircleCollapse R, G) where
  toFun := Quotient.lift Prod.fst (fun _ _ h => h.1)
  continuous_toFun := continuous_fst.quotient_lift _

 
def collapseSection : C(G, CircleCollapse R) where
  toFun g := Quotient.mk _ (g,1)
  continuous_toFun := continuous_quot_mk.comp (continuous_id.prodMk continuous_const)

lemma projection_section : (collapseProjection R).comp (collapseSection R) = ContinuousMap.id G := by
  rfl

lemma section_isEmbedding : IsEmbedding (collapseSection R) :=
  (show Function.LeftInverse (collapseProjection R) (collapseSection R) from fun _ => rfl).isEmbedding
    (collapseProjection R).continuous (collapseSection R).continuous

 
lemma homology_projection_section (n : ℕ) :
    (integralHomologyFunctor n).map (TopCat.ofHom (collapseSection R)) ≫
    (integralHomologyFunctor n).map (TopCat.ofHom (collapseProjection R)) =
    𝟙 (IntegralHomology n G) := by
  rw [← Functor.map_comp]
  change (integralHomologyFunctor n).map (𝟙 (TopCat.of G)) = _
  exact (integralHomologyFunctor n).map_id _

 
def homologyProjection (n : ℕ) : IntegralHomology n (CircleCollapse R) →ₗ[ℤ] IntegralHomology n G :=
  ((integralHomologyFunctor n).map (TopCat.ofHom (collapseProjection R))).hom

def homologySection (n : ℕ) : IntegralHomology n G →ₗ[ℤ] IntegralHomology n (CircleCollapse R) :=
  ((integralHomologyFunctor n).map (TopCat.ofHom (collapseSection R))).hom

lemma homology_projection_section_apply (n : ℕ) (x : IntegralHomology n G) :
    homologyProjection R n (homologySection R n x) = x := by
  exact congrArg (fun f : IntegralHomology n G ⟶ IntegralHomology n G => f x)
    (homology_projection_section R n)

 

def sectionHomologyAddSplitting (n : ℕ) :
    IntegralHomology n (CircleCollapse R) ≃+
      IntegralHomology n G × LinearMap.ker (homologyProjection R n) where
  toFun x := (homologyProjection R n x, ⟨x - homologySection R n (homologyProjection R n x), by
    rw [LinearMap.mem_ker, map_sub, homology_projection_section_apply, sub_self]⟩)
  invFun x := homologySection R n x.1 + x.2.val
  left_inv x := add_sub_cancel _ _
  right_inv x := by
    have hx : homologyProjection R n x.2.val = 0 := x.2.property
    apply Prod.ext
    · change homologyProjection R n (homologySection R n x.1 + x.2.val) = x.1
      rw [map_add, homology_projection_section_apply, hx, add_zero]
    · apply Subtype.ext
      change (homologySection R n x.1 + x.2.val) - homologySection R n
        (homologyProjection R n (homologySection R n x.1 + x.2.val)) = x.2.val
      rw [map_add, homology_projection_section_apply, hx, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · apply Subtype.ext
      change (x+y) - homologySection R n (homologyProjection R n (x+y)) =
        (x - homologySection R n (homologyProjection R n x)) +
        (y - homologySection R n (homologyProjection R n y))
      rw [map_add, map_add]
      abel

 
def sectionHomologySplitting (n : ℕ) :
    IntegralHomology n (CircleCollapse R) ≃ₗ[ℤ]
      IntegralHomology n G × LinearMap.ker (homologyProjection R n) :=
  (sectionHomologyAddSplitting R n).toIntLinearEquiv

 
def sectionSetoid {X : Type} (S : Set X) : Setoid X where
  r x y := x = y ∨ (x ∈ S ∧ y ∈ S)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun h => h.elim (fun h => .inl h.symm) (fun h => .inr h.symm)
    trans := by
      intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inr ⟨hxy.1, hyz.2⟩ }

 
abbrev SectionQuotient := Quotient (sectionSetoid (Set.range (collapseSection R)))

 
def meridianSet : Set (G × Circle) := {p | R p.1 = 0 ∨ p.2 = 1}

 
abbrev RelativeCircleQuotient := Quotient (sectionSetoid (meridianSet R))

lemma mk_mem_section_iff (p : G × Circle) :
    Quotient.mk (collapseSetoid R) p ∈ Set.range (collapseSection R) ↔ p ∈ meridianSet R := by
  constructor
  · rintro ⟨g, hg⟩
    have hh := Quotient.exact hg
    change g = p.1 ∧ (R g = 0 ∨ (1 : Circle) = p.2) at hh
    rcases hh.2 with hr | ha
    · exact Or.inl (hh.1 ▸ hr)
    · exact Or.inr ha.symm
  · intro h
    refine ⟨p.1, Quotient.sound ?_⟩
    refine ⟨rfl, ?_⟩
    exact h.elim Or.inl (fun ha => Or.inr ha.symm)

 
def toRelative : CircleCollapse R → RelativeCircleQuotient R :=
  Quotient.lift (Quotient.mk _ : G × Circle → RelativeCircleQuotient R) (by
    intro p q h
    apply Quotient.sound
    rcases h with ⟨hb, hr | hc⟩
    · exact Or.inr ⟨Or.inl hr, Or.inl (hb ▸ hr)⟩
    · exact Or.inl (Prod.ext hb hc))

lemma continuous_toRelative : Continuous (toRelative R) :=
  continuous_quot_mk.quotient_lift _

lemma toRelative_section_eq (g h : G) :
    toRelative R (collapseSection R g) = toRelative R (collapseSection R h) := by
  apply Quotient.sound
  exact Or.inr ⟨Or.inr rfl, Or.inr rfl⟩

 
def sectionQuotientToRelative : SectionQuotient R → RelativeCircleQuotient R :=
  Quotient.lift (toRelative R) (by
    intro x y h
    rcases h with rfl | ⟨⟨g, rfl⟩, ⟨h, rfl⟩⟩
    · rfl
    · exact toRelative_section_eq R g h)

lemma continuous_sectionQuotientToRelative : Continuous (sectionQuotientToRelative R) :=
  (continuous_toRelative R).quotient_lift _

 
def relativeToSectionQuotient : RelativeCircleQuotient R → SectionQuotient R :=
  Quotient.lift (fun p : G × Circle =>
    Quotient.mk _ (Quotient.mk (collapseSetoid R) p)) (by
    intro p q h
    rcases h with rfl | ⟨hp,hq⟩
    · rfl
    · apply Quotient.sound
      exact Or.inr ⟨(mk_mem_section_iff R p).mpr hp, (mk_mem_section_iff R q).mpr hq⟩)

lemma continuous_relativeToSectionQuotient : Continuous (relativeToSectionQuotient R) :=
  (show Continuous (fun p : G × Circle => Quotient.mk _ (Quotient.mk (collapseSetoid R) p) :
      G × Circle → SectionQuotient R) from
    (show Continuous (Quotient.mk (sectionSetoid (Set.range (collapseSection R)))) from
      continuous_quot_mk).comp
      (show Continuous (Quotient.mk (collapseSetoid R)) from continuous_quot_mk)).quotient_lift _

 

def sectionQuotientHomeomorph : SectionQuotient R ≃ₜ RelativeCircleQuotient R where
  toFun := sectionQuotientToRelative R
  invFun := relativeToSectionQuotient R
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro p
    refine Quotient.inductionOn p ?_
    intro x
    rfl
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro p
    rfl
  continuous_toFun := continuous_sectionQuotientToRelative R
  continuous_invFun := continuous_relativeToSectionQuotient R

end
end AmbientMultiplicity.InnerCircleSection

 

namespace AmbientMultiplicity.SourceInnerPage
noncomputable section
open InnerGeometry CategoryTheory CategoryTheory.Limits

 
def rootSet (R : Base → ℂ → ℂ) (baseRadius : ℝ) (c : ℂ) (radius : ℝ) :
    Set (RootBase baseRadius c radius) :=
  {g | onRootBase R baseRadius c radius g = 0}

abbrev RootRelativeHomology (R : Base → ℂ → ℂ) (baseRadius : ℝ) (c : ℂ)
    (radius : ℝ) (n : ℕ) : ModuleCat ℤ :=
  RelativeSingular.RelativeHomology (rootSet R baseRadius c radius) n

 
def rootBoundary (R : Base → ℂ → ℂ) (baseRadius : ℝ) (c : ℂ)
    (radius : ℝ) (n : ℕ) : RootRelativeHomology R baseRadius c radius (n+1) ⟶
      IntegralHomology n (RootPage R baseRadius c radius) :=
  RelativeSingular.boundary (rootSet R baseRadius c radius) n

 
def rootPushforward (R : Base → ℂ → ℂ) (baseRadius : ℝ) (c : ℂ)
    (radius : ℝ) (n : ℕ) : IntegralHomology n (RootPage R baseRadius c radius) ⟶
      IntegralHomology n (BasePage baseRadius c) :=
  (integralHomologyFunctor n).map (TopCat.ofHom (rootPageProjection R baseRadius c radius))

lemma root_inclusion_projection (R : Base → ℂ → ℂ) (baseRadius : ℝ) (c : ℂ)
    (radius : ℝ) (hradius : 0 ≤ radius) (n : ℕ) :
    HomologicalComplex.homologyMap
      (RelativeSingular.integralChains.map
        (RelativeSingular.inclusion (rootSet R baseRadius c radius))) n ≫
      (rootBaseHomologyIso baseRadius c radius hradius n).hom =
        rootPushforward R baseRadius c radius n := by
  change (integralHomologyFunctor n).map
      (RelativeSingular.inclusion (rootSet R baseRadius c radius)) ≫
    (integralHomologyFunctor n).map (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) = _
  rw [← Functor.map_comp]
  rfl

 

lemma root_projection_kernel (R : Base → ℂ → ℂ) (baseRadius : ℝ) (c : ℂ)
    (radius : ℝ) (hradius : 0 ≤ radius) (n : ℕ) :
    LinearMap.ker (rootPushforward R baseRadius c radius n).hom =
      LinearMap.ker (HomologicalComplex.homologyMap
        (RelativeSingular.integralChains.map
          (RelativeSingular.inclusion (rootSet R baseRadius c radius))) n).hom := by
  rw [← root_inclusion_projection R baseRadius c radius hradius n]
  change LinearMap.ker
    ((rootBaseHomologyIso baseRadius c radius hradius n).hom.hom.comp
      ((integralHomologyFunctor n).map
        (RelativeSingular.inclusion (rootSet R baseRadius c radius))).hom) = _
  apply LinearMap.ker_comp_of_ker_eq_bot
  apply LinearMap.ker_eq_bot.mpr
  exact (ConcreteCategory.bijective_of_isIso
    (rootBaseHomologyIso baseRadius c radius hradius n).hom).injective

 

lemma rootBoundary_range_eq_kernel (R : Base → ℂ → ℂ) (baseRadius : ℝ) (c : ℂ)
    (radius : ℝ) (hradius : 0 ≤ radius) (n : ℕ) :
    LinearMap.range (rootBoundary R baseRadius c radius n).hom =
      LinearMap.ker (rootPushforward R baseRadius c radius n).hom := by
  rw [root_projection_kernel R baseRadius c radius hradius n]
  exact (RelativeSingular.exact_at_subspace (rootSet R baseRadius c radius) n).moduleCat_range_eq_ker

end
end AmbientMultiplicity.SourceInnerPage

 

namespace AmbientMultiplicity.InnerCircleSection
noncomputable section
open InnerGeometry RelativeSingular CategoryTheory CategoryTheory.Limits MonoidalCategory Topology
variable {G : Type} [TopologicalSpace G] (R : G → ℂ)

 
def meridianHomotopy : ContinuousMap.Homotopy (collapseSection R) (collapseSection R) where
  toFun p := Quotient.mk _ (p.2, Circle.exp (2 * Real.pi * (p.1 : ℝ)))
  continuous_toFun := continuous_quot_mk.comp (continuous_snd.prodMk
    (Circle.exp.continuous.comp (continuous_const.mul (continuous_subtype_val.comp continuous_fst))))
  map_zero_left g := by
    change Quotient.mk _ (g, Circle.exp (2 * Real.pi * (0 : ℝ))) = Quotient.mk _ (g, 1)
    simp
  map_one_left g := by
    change Quotient.mk _ (g, Circle.exp (2 * Real.pi * (1 : ℝ))) = Quotient.mk _ (g, 1)
    simp

 
lemma meridianHomotopy_on_root (g : G) (hg : R g = 0) (t : unitInterval) :
    meridianHomotopy R (t,g) = collapseSection R g := by
  exact Quotient.sound ⟨rfl, Or.inl hg⟩

 
lemma meridianHomotopy_over_base (g : G) (t : unitInterval) :
    collapseProjection R (meridianHomotopy R (t,g)) = g := rfl

 

def meridianChainHomotopy : _root_.Homotopy
    (integralChains.map (TopCat.ofHom (collapseSection R)))
    (integralChains.map (TopCat.ofHom (collapseSection R))) :=
  TopCat.Homotopy.singularChainComplexFunctorObjMap (meridianHomotopy R) (ModuleCat.of ℤ ℤ)

 

def meridianPrism (i j : ℕ) :
    (integralChains.obj (TopCat.of G)).X i ⟶
      (integralChains.obj (TopCat.of (CircleCollapse R))).X j :=
  -(meridianChainHomotopy R).hom i j

lemma meridianPrism_dNext_prevD (i : ℕ) :
    dNext i (meridianPrism R) +
      prevD i (meridianPrism R) = 0 := by
  have h := (meridianChainHomotopy R).comm i
  have hzero : dNext i (meridianChainHomotopy R).hom +
      prevD i (meridianChainHomotopy R).hom = 0 := by
    exact add_right_cancel (h.symm.trans (zero_add _).symm)
  change dNext i (-(meridianChainHomotopy R).hom) +
    prevD i (-(meridianChainHomotopy R).hom) = 0
  rw [map_neg, map_neg, ← neg_add, hzero, neg_zero]

 
def zeroSet : Set G := {g | R g = 0}

 
def rootToSection : C(zeroSet R, Set.range (collapseSection R)) where
  toFun g := ⟨collapseSection R g.val, ⟨g.val,rfl⟩⟩
  continuous_toFun := ((collapseSection R).continuous.comp continuous_subtype_val).subtype_mk _

lemma root_meridian_square :
    (RelativeSingular.inclusion (zeroSet R) ▷ TopCat.I) ≫
      TopCat.Homotopy.h (meridianHomotopy R) =
    TopCat.Homotopy.h (TopCat.Homotopy.refl (TopCat.ofHom (rootToSection R))) ≫
      RelativeSingular.inclusion (Set.range (collapseSection R)) := by
  ext p
  exact meridianHomotopy_on_root R p.1.val p.1.property (TopCat.I.homeomorph p.2)

 

lemma meridianPrism_root_zero (i j : ℕ) :
    (integralChains.map (RelativeSingular.inclusion (zeroSet R))).f i ≫
      meridianPrism R i j ≫
        (cokernel.π (integralChains.map
          (RelativeSingular.inclusion (Set.range (collapseSection R))))).f j = 0 := by
  have hs := PrismNaturality.topological_prism_all (meridianHomotopy R)
    (TopCat.Homotopy.refl (TopCat.ofHom (rootToSection R)))
    (RelativeSingular.inclusion (zeroSet R))
    (RelativeSingular.inclusion (Set.range (collapseSection R)))
    (root_meridian_square R) i j
  have hz : (integralChains.map
        (RelativeSingular.inclusion (Set.range (collapseSection R)))).f j ≫
      (cokernel.π (integralChains.map
        (RelativeSingular.inclusion (Set.range (collapseSection R))))).f j = 0 :=
    congrArg (fun f => f.f j) (cokernel.condition (integralChains.map
        (RelativeSingular.inclusion (Set.range (collapseSection R)))))
  unfold meridianPrism meridianChainHomotopy
  rw [← Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp]
  apply neg_eq_zero.mpr
  have hs' : (integralChains.map (RelativeSingular.inclusion (zeroSet R))).f i ≫
      (TopCat.Homotopy.singularChainComplexFunctorObjMap (meridianHomotopy R)
        (ModuleCat.of ℤ ℤ)).hom i j =
    (TopCat.Homotopy.singularChainComplexFunctorObjMap
      (TopCat.Homotopy.refl (TopCat.ofHom (rootToSection R)))
      (ModuleCat.of ℤ ℤ)).hom i j ≫
    (integralChains.map (RelativeSingular.inclusion
      (Set.range (collapseSection R)))).f j := hs
  erw [hs', Category.assoc, hz, comp_zero]

 

def relativeMeridianPrism (i j : ℕ) :
    (relativeChains (zeroSet R)).X i ⟶
      (relativeChains (Set.range (collapseSection R))).X j :=
  relativeDegreeDesc (zeroSet R) i
    (meridianPrism R i j ≫
      (cokernel.π (integralChains.map
        (RelativeSingular.inclusion (Set.range (collapseSection R))))).f j)
    (meridianPrism_root_zero R i j)

@[reassoc]
lemma quotient_comp_relativeMeridianPrism (i j : ℕ) :
    (cokernel.π (integralChains.map (RelativeSingular.inclusion (zeroSet R)))).f i ≫
      relativeMeridianPrism R i j =
    meridianPrism R i j ≫
      (cokernel.π (integralChains.map
        (RelativeSingular.inclusion (Set.range (collapseSection R))))).f j :=
  quotient_comp_relativeDegreeDesc (zeroSet R) i _ _

 
lemma relativeMeridianPrism_dNext_prevD (i : ℕ) :
    dNext i (relativeMeridianPrism R) + prevD i (relativeMeridianPrism R) = 0 := by
  let q := cokernel.π (integralChains.map (RelativeSingular.inclusion (zeroSet R)))
  let q' := cokernel.π (integralChains.map
    (RelativeSingular.inclusion (Set.range (collapseSection R))))
  have hn : (fun a b => q.f a ≫ relativeMeridianPrism R a b) =
      (fun a b => meridianPrism R a b ≫ q'.f b) := by
    funext a b
    exact quotient_comp_relativeMeridianPrism R a b
  apply (cancel_epi (q.f i)).mp
  rw [Preadditive.comp_add, ← dNext_comp_left, ← prevD_comp_left, hn,
    dNext_comp_right, prevD_comp_right, ← Preadditive.add_comp,
    meridianPrism_dNext_prevD, zero_comp, comp_zero]

 
lemma relativeMeridianPrism_shape (i j : ℕ) (h : ¬ i + 1 = j) :
    relativeMeridianPrism R i j = 0 := by
  apply (cancel_epi ((cokernel.π
    (integralChains.map (RelativeSingular.inclusion (zeroSet R)))).f i)).mp
  rw [quotient_comp_relativeMeridianPrism, comp_zero]
  unfold meridianPrism
  rw [(meridianChainHomotopy R).zero i j h, neg_zero, zero_comp]

lemma relativeMeridianPrism_boundary (n : ℕ) :
    (relativeChains (zeroSet R)).d (n+1) n ≫ relativeMeridianPrism R n (n+1) +
      relativeMeridianPrism R (n+1) (n+2) ≫
        (relativeChains (Set.range (collapseSection R))).d (n+2) (n+1) = 0 := by
  have h := relativeMeridianPrism_dNext_prevD R (n+1)
  rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n+1) n by simp),
    prevD_eq _ (show (ComplexShape.down ℕ).Rel (n+2) (n+1) by simp)] at h
  exact h

 

def meridianShortComplexMap (n : ℕ) :
    (relativeChains (zeroSet R)).sc' (n+2) (n+1) n ⟶
      (relativeChains (Set.range (collapseSection R))).sc' (n+3) (n+2) (n+1) where
  τ₁ := -relativeMeridianPrism R (n+2) (n+3)
  τ₂ := relativeMeridianPrism R (n+1) (n+2)
  τ₃ := -relativeMeridianPrism R n (n+1)
  comm₁₂ := by
    change (-relativeMeridianPrism R (n+2) (n+3)) ≫
      (relativeChains (Set.range (collapseSection R))).d (n+3) (n+2) =
      (relativeChains (zeroSet R)).d (n+2) (n+1) ≫ relativeMeridianPrism R (n+1) (n+2)
    rw [Preadditive.neg_comp]
    exact (eq_neg_of_add_eq_zero_left (relativeMeridianPrism_boundary R (n+1))).symm
  comm₂₃ := by
    change relativeMeridianPrism R (n+1) (n+2) ≫
      (relativeChains (Set.range (collapseSection R))).d (n+2) (n+1) =
      (relativeChains (zeroSet R)).d (n+1) n ≫ (-relativeMeridianPrism R n (n+1))
    rw [Preadditive.comp_neg]
    exact eq_neg_of_add_eq_zero_right (relativeMeridianPrism_boundary R n)

 

def relativeMeridianHomology (n : ℕ) :
    RelativeHomology (zeroSet R) (n+1) ⟶
      RelativeHomology (Set.range (collapseSection R)) (n+2) :=
  ((relativeChains (zeroSet R)).homologyIsoSc' (n+2) (n+1) n
    (by simp) (by simp)).hom ≫
  ShortComplex.homologyMap (meridianShortComplexMap R n) ≫
  ((relativeChains (Set.range (collapseSection R))).homologyIsoSc' (n+3) (n+2) (n+1)
    (by simp) (by simp)).inv

end

 

noncomputable section
open InnerGeometry RelativeSingular CategoryTheory CategoryTheory.Limits
variable {G : Type} [TopologicalSpace G] (R : G → ℂ)

 
def sectionRangeRetraction : TopCat.of (CircleCollapse R) ⟶
    TopCat.of (Set.range (collapseSection R)) :=
  TopCat.ofHom {
    toFun := fun x => ⟨collapseSection R (collapseProjection R x), ⟨_,rfl⟩⟩
    continuous_toFun := ((collapseSection R).continuous.comp
      (collapseProjection R).continuous).subtype_mk _ }

lemma inclusion_sectionRangeRetraction :
    RelativeSingular.inclusion (Set.range (collapseSection R)) ≫
      sectionRangeRetraction R = 𝟙 _ := by
  ext x
  obtain ⟨g,hg⟩ := x.property
  show collapseSection R (collapseProjection R x.val) = x.val
  rw [← hg]
  rfl

 

def sectionPairChainSplitting :
    (RelativeSingular.pairSequence (Set.range (collapseSection R))).Splitting :=
  ShortComplex.Splitting.ofExactOfRetraction _
    (RelativeSingular.pairSequence_shortExact _).exact
    (integralChains.map (sectionRangeRetraction R)) (by
      change integralChains.map (RelativeSingular.inclusion (Set.range (collapseSection R))) ≫
        integralChains.map (sectionRangeRetraction R) =
          𝟙 (integralChains.obj (TopCat.of (Set.range (collapseSection R))))
      rw [← CategoryTheory.Functor.map_comp, inclusion_sectionRangeRetraction]
      exact integralChains.map_id _)
    (RelativeSingular.pairSequence_shortExact _).epi_g

 
def sectionRelativeLift (n : ℕ) :
    RelativeHomology (Set.range (collapseSection R)) n ⟶
      IntegralHomology n (CircleCollapse R) :=
  HomologicalComplex.homologyMap (sectionPairChainSplitting R).s n

lemma sectionRelativeLift_toRelative (n : ℕ) :
    sectionRelativeLift R n ≫
      RelativeSingular.toRelativeHomology (Set.range (collapseSection R)) n = 𝟙 _ := by
  unfold sectionRelativeLift RelativeSingular.toRelativeHomology
  erw [← HomologicalComplex.homologyMap_comp]
  change HomologicalComplex.homologyMap
    ((sectionPairChainSplitting R).s ≫
      (RelativeSingular.pairSequence (Set.range (collapseSection R))).g) n = _
  erw [ShortComplex.Splitting.s_g, HomologicalComplex.homologyMap_id]
  rfl

 

def meridianHomology (n : ℕ) : RelativeHomology (zeroSet R) (n+1) ⟶
    IntegralHomology (n+2) (CircleCollapse R) :=
  relativeMeridianHomology R n ≫ sectionRelativeLift R (n+2)

lemma meridianHomology_toRelative (n : ℕ) :
    meridianHomology R n ≫
      RelativeSingular.toRelativeHomology (Set.range (collapseSection R)) (n+2) =
        relativeMeridianHomology R n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun f : RelativeHomology (Set.range (collapseSection R)) (n+2) ⟶
    RelativeHomology (Set.range (collapseSection R)) (n+2) =>
      f (relativeMeridianHomology R n x)) (sectionRelativeLift_toRelative R (n+2))

 
def sectionBaseProjection : TopCat.of (Set.range (collapseSection R)) ⟶ TopCat.of G :=
  TopCat.ofHom ⟨fun x => collapseProjection R x.val,
    (collapseProjection R).continuous.comp continuous_subtype_val⟩

lemma sectionRetraction_base :
    sectionRangeRetraction R ≫ sectionBaseProjection R =
      TopCat.ofHom (collapseProjection R) := by
  ext x
  rfl

lemma sectionRelativeLift_projection (n : ℕ) :
    sectionRelativeLift R n ≫
      (integralHomologyFunctor n).map (TopCat.ofHom (collapseProjection R)) = 0 := by
  change HomologicalComplex.homologyMap (sectionPairChainSplitting R).s n ≫
    HomologicalComplex.homologyMap
      (integralChains.map (TopCat.ofHom (collapseProjection R))) n = 0
  erw [← HomologicalComplex.homologyMap_comp]
  have hp : integralChains.map (TopCat.ofHom (collapseProjection R)) =
      integralChains.map (sectionRangeRetraction R) ≫
        integralChains.map (sectionBaseProjection R) := by
    rw [← CategoryTheory.Functor.map_comp, sectionRetraction_base]
  have hs : (sectionPairChainSplitting R).s ≫
      integralChains.map (sectionRangeRetraction R) = 0 :=
    (sectionPairChainSplitting R).s_r
  erw [hp, ← Category.assoc, hs, zero_comp, HomologicalComplex.homologyMap_zero]

lemma meridianHomology_projection (n : ℕ) :
    meridianHomology R n ≫
      (integralHomologyFunctor (n+2)).map (TopCat.ofHom (collapseProjection R)) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun f : RelativeHomology (Set.range (collapseSection R)) (n+2) ⟶
    IntegralHomology (n+2) G =>
      f (relativeMeridianHomology R n x)) (sectionRelativeLift_projection R (n+2))

 

def meridianKernelAddHom (n : ℕ) :
    RelativeHomology (zeroSet R) (n+1) →+
      LinearMap.ker (homologyProjection R (n+2)) where
  toFun x := ⟨meridianHomology R n x, by
    rw [LinearMap.mem_ker]
    exact congrArg (fun f : RelativeHomology (zeroSet R) (n+1) ⟶
      IntegralHomology (n+2) G => f x) (meridianHomology_projection R n)⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _

def meridianKernelHomology (n : ℕ) :
    RelativeHomology (zeroSet R) (n+1) →ₗ[ℤ]
      LinearMap.ker (homologyProjection R (n+2)) :=
  { meridianKernelAddHom R n with
    map_smul' := by
      intro c x
      convert! (meridianKernelAddHom R n).map_zsmul c x using 1
      · exact congrArg (meridianKernelAddHom R n) (int_smul_eq_zsmul _ _ _)
    }

end
end AmbientMultiplicity.InnerCircleSection

end OAI
