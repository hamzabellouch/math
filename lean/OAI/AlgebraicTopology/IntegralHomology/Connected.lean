import OAI.AlgebraicTopology.IntegralHomology.Excision
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

namespace OAI

noncomputable section

namespace Kaplansky

/-! Connected-cover homology, degree-zero components, and degree-one generators. -/

section
open CategoryTheory Limits

/-- A contractible subspace has zero relative connecting boundary in positive degree. -/
theorem relativeHomologyBoundary_eq_zero_of_contractible {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i] [ContractibleSpace A] (n : ℕ) (hn : n ≠ 0) :
    relativeHomologyBoundary i n = 0 :=
  (integralSingularHomology_isZero_contractible A n hn).eq_of_tgt _ _

/-- Localization to a relative pair is an isomorphism above degree one when
its removed subspace is contractible. The map is the actual quotient map. -/
theorem absoluteToRelative_bijective_of_contractible {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i] [ContractibleSpace A] (n : ℕ) (hn : n ≠ 0) :
    Function.Bijective (absoluteToRelative i (n+1)) := by
  constructor
  · apply (absoluteToRelative i (n+1)).hom.ker_eq_bot.mp
    rw [← (relativeHomology_exact_at_absolute i (n+1)).moduleCat_range_eq_ker]
    have hz : (integralSingularHomology (n+1)).map i = 0 :=
      (integralSingularHomology_isZero_contractible A (n+1) (Nat.succ_ne_zero n)).eq_of_src _ _
    change LinearMap.range ((integralSingularHomology (n+1)).map i).hom = ⊥
    rw [hz]
    exact LinearMap.range_zero
  · intro c
    apply (relativeClass_lifts_iff i n c).mp
    rw [relativeHomologyBoundary_eq_zero_of_contractible i n hn]
    rfl

def contractibleSubspaceLocalizationIso {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i] [ContractibleSpace A] (n : ℕ) (hn : n ≠ 0) :
    (integralSingularHomology (n+1)).obj X ≅ relativeSingularHomology i (n+1) :=
  (LinearEquiv.ofBijective (absoluteToRelative i (n+1)).hom
    (absoluteToRelative_bijective_of_contractible i n hn)).toModuleIso

theorem contractibleSubspaceLocalizationIso_hom {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i] [ContractibleSpace A] (n : ℕ) (hn : n ≠ 0) :
    (contractibleSubspaceLocalizationIso i n hn).hom = absoluteToRelative i (n+1) := rfl

end

section
open CategoryTheory Limits HomologicalComplex AlgebraicTopology Simplicial

private abbrev pointComponentIso (X : TopCat.{0}) :
    (integralSingularHomology 0).obj X ≅
      ∐ fun _ : (TopCat.toSSet.obj X).π₀ => ModuleCat.of ℤ ℤ :=
  (TopCat.toSSet.obj X).homology₀Iso (ModuleCat.of ℤ ℤ)

private abbrev pointAugmentation (X : TopCat.{0}) :
    (integralSingularHomology 0).obj X ⟶ ModuleCat.of ℤ ℤ :=
  X.singularHomology₀ε (ModuleCat.of ℤ ℤ)

/-- The actual integral H₀ class of a point, expressed as a map out of ℤ. -/
def pointHomology (X : TopCat.{0}) (x : X) :
    ModuleCat.of ℤ ℤ ⟶ (integralSingularHomology 0).obj X :=
  ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).liftCycles
    ((TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x))
    0 (by simp) (by simp) ≫ ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).homologyπ 0

@[reassoc (attr := simp)]
theorem pointHomology_component (X : TopCat.{0}) (x : X) :
    pointHomology X x ≫ (pointComponentIso X).hom =
      Sigma.ι (fun _ : (TopCat.toSSet.obj X).π₀ => ModuleCat.of ℤ ℤ)
        (SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm x)) :=
  by
    dsimp only [pointHomology, pointComponentIso]
    erw [Category.assoc]
    exact (SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom
      (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ) (TopCat.toSSetObj₀Equiv.symm x))

@[reassoc (attr := simp)]
theorem pointHomology_map {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    pointHomology X x ≫ (integralSingularHomology 0).map f = pointHomology Y (f x) := by
  unfold pointHomology
  change (_ ≫ _) ≫ homologyMap (integralSingularChains.map f) 0 = _
  erw [Category.assoc, homologyπ_naturality, ← Category.assoc,
    liftCycles_comp_cyclesMap]
  have h : (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x) ≫
      (integralSingularChains.map f).f 0 =
      (TopCat.toSSet.obj Y).ιChainComplex (TopCat.toSSetObj₀Equiv.symm (f x)) :=
    SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
      (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ) _
  simp only [h]
  rfl

/-- Points in the same path component give equal integral H₀ classes. -/
theorem pointHomology_eq_of_joined (X : TopCat.{0}) {x y : X} (h : Joined x y) :
    pointHomology X x = pointHomology X y := by
  apply (cancel_mono (pointComponentIso X).hom).mp
  rw [pointHomology_component, pointHomology_component]
  have h' := congrArg TopCat.zerothHomotopyEquiv (ZerothHomotopy.sound h.somePath)
  exact congrArg (Sigma.ι _) h'

/-- Distinct path components are separated by the actual integral H₀ class. -/
theorem pointHomology_ne_of_not_joined (X : TopCat.{0}) {x y : X}
    (h : ¬ Joined x y) : pointHomology X x ≠ pointHomology X y := by
  classical
  intro he
  let a := SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm x)
  let b := SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm y)
  have hab : a ≠ b := by
    intro hab
    have hz : ZerothHomotopy.mk x = ZerothHomotopy.mk y :=
      TopCat.zerothHomotopyEquiv.injective hab
    exact h (Quotient.exact hz)
  let test : (∐ fun _ : (TopCat.toSSet.obj X).π₀ => ModuleCat.of ℤ ℤ) ⟶
      ModuleCat.of ℤ ℤ := Sigma.desc (fun c => if c = a then 𝟙 _ else 0)
  have he' := congrArg (fun k => k ≫
    (pointComponentIso X).hom ≫ test) he
  simp only [pointHomology_component_assoc] at he'
  have hi : (𝟙 (ModuleCat.of ℤ ℤ)) = 0 := by
    simpa [test, a, b, hab, Ne.symm hab] using he'
  have hn := ConcreteCategory.congr_hom hi (1 : ℤ)
  norm_num at hn

/-- All actual H₀ classes are determined by their values on point classes. -/
theorem pointHomology_hom_ext (X : TopCat.{0}) {T : ModuleCat.{0} ℤ}
    {f g : (integralSingularHomology 0).obj X ⟶ T}
    (h : ∀ x, pointHomology X x ≫ f = pointHomology X x ≫ g) : f = g := by
  let e := pointComponentIso X
  apply (cancel_epi e.inv).mp
  apply Sigma.hom_ext
  intro c
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective c
  obtain ⟨x, rfl⟩ := TopCat.toSSetObj₀Equiv.symm.surjective s
  have hp : Sigma.ι _ (SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm x)) ≫ e.inv =
      pointHomology X x := by
    rw [← pointHomology_component, Category.assoc, e.hom_inv_id]
    exact Category.comp_id _
  simpa only [← Category.assoc, hp] using h x

/-- The integral coefficient of one specified path component. -/
def componentCoefficient (X : TopCat.{0}) (a : X) :
    (integralSingularHomology 0).obj X ⟶ ModuleCat.of ℤ ℤ := by
  classical
  exact (pointComponentIso X).hom ≫
    Sigma.desc (fun c => if c = SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm a) then 𝟙 _ else 0)

@[reassoc (attr := simp)]
theorem pointHomology_coefficient_self (X : TopCat.{0}) (a : X) :
    pointHomology X a ≫ componentCoefficient X a = 𝟙 _ := by
  simp [componentCoefficient]

@[reassoc (attr := simp)]
theorem pointHomology_coefficient_other (X : TopCat.{0}) (a b : X) (hab : ¬ Joined a b) :
    pointHomology X a ≫ componentCoefficient X b = 0 := by
  have h : SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm a) ≠
      SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm b) := by
    intro h
    exact hab (Quotient.exact (TopCat.zerothHomotopyEquiv.injective h))
  simp [componentCoefficient, h]

/-- The augmentation takes each integral point class to one. -/
@[reassoc (attr := simp)]
theorem pointHomology_augmentation (X : TopCat.{0}) (a : X) :
    pointHomology X a ≫ pointAugmentation X = 𝟙 _ := by
  dsimp only [pointHomology, pointAugmentation, TopCat.singularHomology₀ε]
  erw [Category.assoc]
  exact (SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
      (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ) (TopCat.toSSetObj₀Equiv.symm a))

/-- For a space with exactly these two path components, their two point
classes span all integral H₀, with canonical integral coefficients. -/
theorem twoComponent_decomposition (X : TopCat.{0}) (a b : X) (hab : ¬ Joined a b)
    (hcover : ∀ x : X, Joined x a ∨ Joined x b) :
    componentCoefficient X a ≫ pointHomology X a +
      componentCoefficient X b ≫ pointHomology X b = 𝟙 _ := by
  apply pointHomology_hom_ext X
  intro x
  rcases hcover x with hx | hx
  · rw [pointHomology_eq_of_joined X hx]
    simp [Preadditive.comp_add, pointHomology_coefficient_other_assoc X a b hab]
  · rw [pointHomology_eq_of_joined X hx]
    have hba : ¬ Joined b a := fun h => hab h.symm
    simp [Preadditive.comp_add, pointHomology_coefficient_other_assoc X b a hba]

theorem twoComponent_decomposition_apply (X : TopCat.{0}) (a b : X) (hab : ¬ Joined a b)
    (hcover : ∀ x : X, Joined x a ∨ Joined x b)
    (z : (integralSingularHomology 0).obj X) :
    pointHomology X a (componentCoefficient X a z) +
      pointHomology X b (componentCoefficient X b z) = z :=
  ConcreteCategory.congr_hom (twoComponent_decomposition X a b hab hcover) z

end

section
open CategoryTheory Limits HomologicalComplex

section

private theorem additiveFunctor_biprod_detect_zero
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} [HasBinaryBiproduct X Y]
    {T : D} (f : T ⟶ F.obj (X ⊞ Y))
    (h₁ : f ≫ F.map biprod.fst = 0) (h₂ : f ≫ F.map biprod.snd = 0) : f = 0 := by
  have he := congrArg (fun g : X ⊞ Y ⟶ X ⊞ Y => f ≫ F.map g)
    (biprod.total (X := X) (Y := Y))
  simp only [Functor.map_add, Functor.map_comp, Preadditive.comp_add,
    ← Category.assoc] at he
  erw [F.map_id, Category.comp_id] at he
  rw [h₁, h₂, zero_comp, zero_comp, add_zero] at he
  exact he.symm

/-- Homology of a biproduct is jointly detected by its two projections. -/
theorem homology_biprod_detect_zero {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    {T : ModuleCat.{0} ℤ} (n : ℕ) (f : T ⟶ (C ⊞ D).homology n)
    (h₁ : f ≫ homologyMap biprod.fst n = 0)
    (h₂ : f ≫ homologyMap biprod.snd n = 0) : f = 0 := by
  exact additiveFunctor_biprod_detect_zero
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n) f h₁ h₂

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- A difference of two point classes in the intersection is killed by
both inclusion maps when both cover members are path connected. -/
theorem pointDifference_mayerVietoris_zero [PathConnectedSpace U] [PathConnectedSpace V]
    (a b : ↥(U ∩ V)) :
    (pointHomology (TopCat.of ↥(U ∩ V)) a - pointHomology (TopCat.of ↥(U ∩ V)) b) ≫
      homologyMap (smallMayerVietorisSequence U V).f 0 = 0 := by
  let c := pointHomology (TopCat.of ↥(U ∩ V)) a - pointHomology (TopCat.of ↥(U ∩ V)) b
  apply homology_biprod_detect_zero 0
  · erw [Category.assoc, ← homologyMap_comp]
    have hf : (smallMayerVietorisSequence U V).f ≫ biprod.fst =
        integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) :=
      biprod.lift_fst _ _
    rw [hf]
    change c ≫ (integralSingularHomology 0).map _ = _
    simp only [c, Preadditive.sub_comp, pointHomology_map]
    exact sub_eq_zero.mpr (pointHomology_eq_of_joined _ (PathConnectedSpace.joined _ _))
  · erw [Category.assoc, ← homologyMap_comp]
    have hf : (smallMayerVietorisSequence U V).f ≫ biprod.snd =
        -integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V)) :=
      biprod.lift_snd _ _
    erw [hf, homologyMap_neg, Preadditive.comp_neg]
    change -(c ≫ (integralSingularHomology 0).map _) = _
    simp only [c, Preadditive.sub_comp, pointHomology_map]
    rw [pointHomology_eq_of_joined _ (PathConnectedSpace.joined _ _), sub_self, neg_zero]
    rfl

/-- Two distinct path components in the intersection of a path-connected
open cover produce a genuinely nonzero integral H₁ class. -/
theorem openCover_homologyOne_nonzero [PathConnectedSpace U] [PathConnectedSpace V]
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (a b : ↥(U ∩ V)) (hab : ¬ Joined a b) :
    ∃ z : (integralSingularHomology 1).obj (TopCat.of X), z ≠ 0 := by
  let c := pointHomology (TopCat.of ↥(U ∩ V)) a - pointHomology (TopCat.of ↥(U ∩ V)) b
  have hc : c (1 : ℤ) ≠ 0 := by
    intro hz
    have hc0 : c = 0 := ModuleCat.hom_ext (LinearMap.ext_ring hz)
    exact pointHomology_ne_of_not_joined _ hab (sub_eq_zero.mp hc0)
  have hk : c (1 : ℤ) ∈ LinearMap.ker (homologyMap (smallMayerVietorisSequence U V).f 0).hom := by
    change homologyMap (smallMayerVietorisSequence U V).f 0 (c (1 : ℤ)) = 0
    exact ConcreteCategory.congr_hom (pointDifference_mayerVietoris_zero U V a b) (1 : ℤ)
  have hex := (smallMayerVietoris_exact_at_intersection U V 0).moduleCat_range_eq_ker
  rw [← hex] at hk
  obtain ⟨z, hz⟩ := hk
  have hz0 : z ≠ 0 := by
    intro he
    apply hc
    rw [← hz, he, map_zero]
    rfl
  let e := openCoverSmallHomologyIso U V hU hV hUV 1
  refine ⟨e.hom z, ?_⟩
  intro h
  apply hz0
  exact (ModuleCat.mono_iff_injective e.hom).mp inferInstance
    (h.trans (e.hom.hom.map_zero).symm)

end

section
variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The two intersection coefficients sum to the augmentation after inclusion. -/
theorem twoComponent_inclusion_augmentation (a b : ↥(U ∩ V)) (hab : ¬ Joined a b)
    (hcover : ∀ x : ↥(U ∩ V), Joined x a ∨ Joined x b) :
    componentCoefficient (TopCat.of ↥(U ∩ V)) a + componentCoefficient (TopCat.of ↥(U ∩ V)) b =
      (integralSingularHomology 0).map
        (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) ≫
        pointAugmentation (TopCat.of U) := by
  apply pointHomology_hom_ext
  intro x
  rcases hcover x with hx | hx
  · rw [pointHomology_eq_of_joined _ hx]
    simp [Preadditive.comp_add, pointHomology_coefficient_other (TopCat.of ↥(U ∩ V)) a b hab]
  · rw [pointHomology_eq_of_joined _ hx]
    have hba : ¬ Joined b a := fun h => hab h.symm
    simp [Preadditive.comp_add, pointHomology_coefficient_other (TopCat.of ↥(U ∩ V)) b a hba]

/-- Elements killed by the intersection-to-sum map have opposite coefficients. -/
theorem twoComponent_mayerVietoris_kernel (a b : ↥(U ∩ V)) (hab : ¬ Joined a b)
    (hcover : ∀ x : ↥(U ∩ V), Joined x a ∨ Joined x b)
    (z : (integralSingularHomology 0).obj (TopCat.of ↥(U ∩ V)))
    (hz : homologyMap (smallMayerVietorisSequence U V).f 0 z = 0) :
    componentCoefficient (TopCat.of ↥(U ∩ V)) a z +
      componentCoefficient (TopCat.of ↥(U ∩ V)) b z = 0 := by
  have hf : homologyMap (smallMayerVietorisSequence U V).f 0 ≫ homologyMap biprod.fst 0 =
      (integralSingularHomology 0).map
        (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) := by
    erw [← homologyMap_comp]
    congr 1
    exact biprod.lift_fst _ _
  have hz' : (integralSingularHomology 0).map
      (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) z = 0 := by
    erw [← hf, ModuleCat.comp_apply]
    erw [hz]
    exact map_zero _
  have h := ConcreteCategory.congr_hom (twoComponent_inclusion_augmentation U V a b hab hcover) z
  change componentCoefficient (TopCat.of ↥(U ∩ V)) a z +
      componentCoefficient (TopCat.of ↥(U ∩ V)) b z =
      pointAugmentation (TopCat.of U)
        ((integralSingularHomology 0).map
          (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) z) at h
  erw [hz', map_zero] at h
  exact h

/-- The coefficient of the first intersection component after the actual
Mayer–Vietoris boundary. This fixes an integral sign convention. -/
def smallMayerVietorisOneCoordinate (a : ↥(U ∩ V)) :
    (smallSingularChains U V).homology 1 ⟶ ModuleCat.of ℤ ℤ :=
  smallMayerVietorisBoundary U V 0 ≫ componentCoefficient (TopCat.of ↥(U ∩ V)) a

/-- Exact integral H₁ calculation for two contractible sets whose intersection
has exactly two path components. No homology or normalization premise. -/
theorem smallMayerVietorisOneCoordinate_bijective [ContractibleSpace U] [ContractibleSpace V]
    (a b : ↥(U ∩ V)) (hab : ¬ Joined a b)
    (hcover : ∀ x : ↥(U ∩ V), Joined x a ∨ Joined x b) :
    Function.Bijective (smallMayerVietorisOneCoordinate U V a) := by
  let δ := smallMayerVietorisBoundary U V 0
  let : Mono δ := (smallMayerVietorisSequence_shortExact U V).mono_δ 1 0 rfl
    (smallMayerVietoris_sum_isZero U V 1 (by decide))
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    change componentCoefficient (TopCat.of ↥(U ∩ V)) a (δ z) = 0 at hz
    have hk : homologyMap (smallMayerVietorisSequence U V).f 0 (δ z) = 0 :=
      ConcreteCategory.congr_hom
        ((smallMayerVietorisSequence_shortExact U V).δ_comp 1 0 rfl) z
    have hsum := twoComponent_mayerVietoris_kernel U V a b hab hcover (δ z) hk
    rw [hz, zero_add] at hsum
    have hd := twoComponent_decomposition_apply _ a b hab hcover (δ z)
    rw [hz, hsum, map_zero, map_zero, add_zero] at hd
    exact (ModuleCat.mono_iff_injective δ).mp inferInstance
      (hd.symm.trans δ.hom.map_zero.symm)
  · intro k
    let c := pointHomology (TopCat.of ↥(U ∩ V)) a - pointHomology (TopCat.of ↥(U ∩ V)) b
    have hk : c k ∈ LinearMap.ker (homologyMap (smallMayerVietorisSequence U V).f 0).hom := by
      change homologyMap (smallMayerVietorisSequence U V).f 0 (c k) = 0
      exact ConcreteCategory.congr_hom (pointDifference_mayerVietoris_zero U V a b) k
    rw [← (smallMayerVietoris_exact_at_intersection U V 0).moduleCat_range_eq_ker] at hk
    obtain ⟨z, hz⟩ := hk
    refine ⟨z, ?_⟩
    change componentCoefficient (TopCat.of ↥(U ∩ V)) a (δ z) = k
    change δ z = c k at hz
    rw [hz]
    have hba : ¬ Joined b a := fun h => hab h.symm
    have he : c ≫ componentCoefficient (TopCat.of ↥(U ∩ V)) a = 𝟙 _ := by
      simp [c, Preadditive.sub_comp, pointHomology_coefficient_other (TopCat.of ↥(U ∩ V)) b a hba]
    exact ConcreteCategory.congr_hom he k

def smallMayerVietorisOneIso [ContractibleSpace U] [ContractibleSpace V]
    (a b : ↥(U ∩ V)) (hab : ¬ Joined a b)
    (hcover : ∀ x : ↥(U ∩ V), Joined x a ∨ Joined x b) :
    (smallSingularChains U V).homology 1 ≅ ModuleCat.of ℤ ℤ := by
  haveI := (ConcreteCategory.isIso_iff_bijective (smallMayerVietorisOneCoordinate U V a)).mpr
    (smallMayerVietorisOneCoordinate_bijective U V a b hab hcover)
  exact asIso (smallMayerVietorisOneCoordinate U V a)

/-- Full integral H₁ with the sign fixed by the ordered two intersection components. -/
def openCoverMayerVietorisOneIso [ContractibleSpace U] [ContractibleSpace V]
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (a b : ↥(U ∩ V)) (hab : ¬ Joined a b)
    (hcover : ∀ x : ↥(U ∩ V), Joined x a ∨ Joined x b) :
    (integralSingularHomology 1).obj (TopCat.of X) ≅ ModuleCat.of ℤ ℤ :=
  (openCoverSmallHomologyIso U V hU hV hUV 1).symm ≪≫
    smallMayerVietorisOneIso U V a b hab hcover

end

/-- An inclusion (indeed any map) from a path-connected space is injective
on integral H₀. The augmentation provides an explicit left inverse. -/
theorem integralHomologyZero_map_injective {A X : TopCat.{0}}
    [PathConnectedSpace A] (f : A ⟶ X) :
    Function.Injective ((integralSingularHomology 0).map f) := by
  let a : A := Classical.choice (inferInstance : Nonempty A)
  have hs : (integralSingularHomology 0).map f ≫
      pointAugmentation X ≫ pointHomology A a = 𝟙 _ := by
    apply pointHomology_hom_ext A
    intro x
    simp only [← Category.assoc, pointHomology_map, pointHomology_augmentation,
      Category.id_comp, Category.comp_id]
    exact pointHomology_eq_of_joined A (PathConnectedSpace.joined a x)
  intro x y h
  have hx := ConcreteCategory.congr_hom hs x
  have hy := ConcreteCategory.congr_hom hs y
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hx hy
  rw [h] at hx
  exact hx.symm.trans hy

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Two contractible open sets with path-connected intersection have zero
integral H₁. The connected-intersection hypothesis is essential. -/
theorem openCover_homologyOne_isZero [ContractibleSpace U] [ContractibleSpace V]
    [PathConnectedSpace ↥(U ∩ V)]
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    IsZero ((integralSingularHomology 1).obj (TopCat.of X)) := by
  let δ := smallMayerVietorisBoundary U V 0
  let : Mono δ := (smallMayerVietorisSequence_shortExact U V).mono_δ 1 0 rfl
    (smallMayerVietoris_sum_isZero U V 1 (by decide))
  have hf : homologyMap (smallMayerVietorisSequence U V).f 0 ≫ homologyMap biprod.fst 0 =
      (integralSingularHomology 0).map
        (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) := by
    erw [← homologyMap_comp]
    congr 1
    exact biprod.lift_fst _ _
  have hz : IsZero ((smallSingularChains U V).homology 1) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro z
    have hk : homologyMap (smallMayerVietorisSequence U V).f 0 (δ z) = 0 :=
      ConcreteCategory.congr_hom
        ((smallMayerVietorisSequence_shortExact U V).δ_comp 1 0 rfl) z
    have hi : (integralSingularHomology 0).map
        (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) (δ z) = 0 := by
      erw [← hf, ModuleCat.comp_apply]
      erw [hk]
      exact map_zero _
    have hd : δ z = 0 := integralHomologyZero_map_injective _ (hi.trans (map_zero _).symm)
    exact (ModuleCat.mono_iff_injective δ).mp inferInstance (hd.trans (map_zero _).symm)
  exact hz.of_iso (openCoverSmallHomologyIso U V hU hV hUV 1).symm

end

open CategoryTheory Limits
section

/-- A connected removed subspace makes the degree-one connecting map zero. -/
theorem relativeHomologyBoundary_zero_connected {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i] [PathConnectedSpace A] :
    relativeHomologyBoundary i 0 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply integralHomologyZero_map_injective i
  exact (ConcreteCategory.congr_hom (relativeHomologyBoundary_inclusion i 0) z).trans
    (map_zero _).symm

/-- A connected subspace of a contractible ambient space has zero relative H₁. -/
theorem relativeHomologyOne_isZero {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    [PathConnectedSpace A] [ContractibleSpace X] :
    IsZero (relativeSingularHomology i 1) := by
  let : Mono (relativeHomologyBoundary i 0) :=
    (relativeChainSequence_shortExact i).mono_δ 1 0 rfl
      (integralSingularHomology_isZero_contractible X 1 (by decide))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro z
  apply (ModuleCat.mono_iff_injective (relativeHomologyBoundary i 0)).mp inferInstance
  rw [relativeHomologyBoundary_zero_connected]
  rfl

/-- The contractible-subspace localization theorem also holds in degree one;
the low-degree proof uses H₀ injectivity, not a false H₀ vanishing claim. -/
def contractibleSubspaceLocalizationOneIso {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i] [ContractibleSpace A] :
    (integralSingularHomology 1).obj X ≅ relativeSingularHomology i 1 := by
  apply (LinearEquiv.ofBijective (absoluteToRelative i 1).hom ?_).toModuleIso
  constructor
  · apply (absoluteToRelative i 1).hom.ker_eq_bot.mp
    rw [← (relativeHomology_exact_at_absolute i 1).moduleCat_range_eq_ker]
    change LinearMap.range ((integralSingularHomology 1).map i).hom = ⊥
    have hz : (integralSingularHomology 1).map i = 0 :=
      (integralSingularHomology_isZero_contractible A 1 (by decide)).eq_of_src _ _
    rw [hz]
    exact LinearMap.range_zero
  · intro z
    apply (relativeClass_lifts_iff i 0 z).mp
    rw [relativeHomologyBoundary_zero_connected]
    rfl

theorem contractibleSubspaceLocalizationOneIso_hom {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i] [ContractibleSpace A] :
    (contractibleSubspaceLocalizationOneIso i).hom = absoluteToRelative i 1 := rfl

/-- Relative H₀ vanishes if the ambient space is path connected and the
removed subspace is nonempty. -/
theorem relativeHomologyZero_isZero {A X : TopCat.{0}} (i : A ⟶ X)
    [PathConnectedSpace X] [Nonempty A] :
    IsZero (relativeSingularHomology i 0) := by
  let a : A := Classical.choice (inferInstance : Nonempty A)
  have hz : absoluteToRelative i 0 = 0 := by
    apply pointHomology_hom_ext X
    intro x
    rw [pointHomology_eq_of_joined X (PathConnectedSpace.joined x (i a))]
    rw [← pointHomology_map i a, Category.assoc, inclusion_absoluteToRelative]
    simp
  let : Epi (absoluteToRelative i 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel (relativeChainProjection i) 0
      (by intro j; simp)
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_epi (absoluteToRelative i 0)).mp
  rw [hz, zero_comp, zero_comp]

end

end Kaplansky

end

end OAI
