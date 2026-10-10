import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Simplicial.SingularKanComplex
import OAI.CategoryTheory.Thomason.Simplicial.SingularPathSpaceAdjunction
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages

namespace OAI

section

/-! # Path-space compatibility with actual weak equivalences -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- Evaluation at the initial endpoint of an unrestricted continuous path. -/
def continuousPathStart (X : TopCat.{0}) : continuousPathSpace X ⟶ X :=
  TopCat.ofHom ⟨fun γ : C(unitInterval, X) => γ 0, by fun_prop⟩

/-- The constant-path section of initial evaluation. -/
def continuousPathConstant (X : TopCat.{0}) : X ⟶ continuousPathSpace X :=
  TopCat.ofHom ContinuousMap.const'

/-- Shrinking the time coordinate contracts each path to its initial point. -/
def continuousPathContraction (X : TopCat.{0}) :
    ((continuousPathConstant X).hom.comp (continuousPathStart X).hom).Homotopy
      (ContinuousMap.id (continuousPathSpace X)) where
  toFun z := (show C(unitInterval, X) from z.2).comp
    ⟨fun s => z.1 * s, by fun_prop⟩
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × C(unitInterval, X)) × unitInterval =>
      z.1.2 (z.1.1 * z.2))
    fun_prop
  map_zero_left γ := by
    apply ContinuousMap.ext
    intro s
    change (show C(unitInterval, X) from γ) (0 * s) =
      (show C(unitInterval, X) from γ) 0
    rw [zero_mul]
  map_one_left γ := by
    apply ContinuousMap.ext
    intro s
    change (show C(unitInterval, X) from γ) (1 * s) =
      (show C(unitInterval, X) from γ) s
    rw [one_mul]

/-- Initial evaluation is an actual homotopy equivalence, naturally in the space. -/
def continuousPathStartEquiv (X : TopCat.{0}) :
    ContinuousMap.HomotopyEquiv (continuousPathSpace X) X where
  toFun := (continuousPathStart X).hom
  invFun := (continuousPathConstant X).hom
  left_inv := ⟨continuousPathContraction X⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl _⟩

theorem continuousPathStart_naturality {X Y : TopCat.{0}} (p : X ⟶ Y) :
    continuousPathMap p ≫ continuousPathStart Y = continuousPathStart X ≫ p := rfl

/-- Forming the unrestricted path space preserves and reflects the actual
topological weak-equivalence test. -/
theorem continuousPathMap_weak_iff {X Y : TopCat.{0}} (p : X ⟶ Y) :
    IsWeakHomotopyEquivalence (continuousPathMap p).hom ↔
      IsWeakHomotopyEquivalence p.hom := by
  have hx : topologicalWeakEquivalences (continuousPathStart X) :=
    homotopyEquiv_isWeakHomotopyEquivalence (continuousPathStartEquiv X)
  have hy : topologicalWeakEquivalences (continuousPathStart Y) :=
    homotopyEquiv_isWeakHomotopyEquivalence (continuousPathStartEquiv Y)
  constructor
  · intro hp
    apply topologicalWeakEquivalences.of_precomp (continuousPathStart X) p hx
    rw [← continuousPathStart_naturality]
    exact topologicalWeakEquivalences.comp_mem _ _ hp hy
  · intro hp
    apply topologicalWeakEquivalences.of_postcomp (continuousPathMap p)
      (continuousPathStart Y) hy
    rw [continuousPathStart_naturality]
    exact topologicalWeakEquivalences.comp_mem _ _ hx hp

/-- The same equivalence holds for the actual realization weak test on singular
maps, without assuming a general singular comparison theorem. -/
theorem singularPathMap_weak_iff {X Y : TopCat.{0}} (p : X ⟶ Y) :
    realizationWeakEquivalences (TopCat.toSSet.map (continuousPathMap p)) ↔
      realizationWeakEquivalences (TopCat.toSSet.map p) := by
  have hx : realizationWeakEquivalences (TopCat.toSSet.map (continuousPathStart X)) :=
    singular_homotopy_equivalence_weak (continuousPathStartEquiv X)
  have hy : realizationWeakEquivalences (TopCat.toSSet.map (continuousPathStart Y)) :=
    singular_homotopy_equivalence_weak (continuousPathStartEquiv Y)
  have hn : TopCat.toSSet.map (continuousPathMap p) ≫
      TopCat.toSSet.map (continuousPathStart Y) =
      TopCat.toSSet.map (continuousPathStart X) ≫ TopCat.toSSet.map p := by
    rw [← Functor.map_comp, ← Functor.map_comp, continuousPathStart_naturality]
  constructor
  · intro hp
    apply realizationWeakEquivalences.of_precomp
      (TopCat.toSSet.map (continuousPathStart X)) _ hx
    rw [← hn]
    exact realizationWeakEquivalences.comp_mem _ _ hp hy
  · intro hp
    apply realizationWeakEquivalences.of_postcomp _
      (TopCat.toSSet.map (continuousPathStart Y)) hy
    rw [hn]
    exact realizationWeakEquivalences.comp_mem _ _ hx hp

end

end Thomason.Construction

end

section

/-! # The actual mapping-path space and its homotopy-equivalent inclusion -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

def mappingPathSpace {X Y : TopCat.{0}} (p : X ⟶ Y) : TopCat.{0} :=
  TopCat.of {z : X × C(unitInterval, Y) // z.2 0 = p.hom z.1}

def mappingPathInclusion {X Y : TopCat.{0}} (p : X ⟶ Y) : X ⟶ mappingPathSpace p :=
  TopCat.ofHom {
    toFun x := ⟨(x, ContinuousMap.const _ (p.hom x)), rfl⟩
    continuous_toFun := (continuous_id.prodMk
      ((ContinuousMap.const' : C(Y, C(unitInterval, Y))).continuous.comp p.hom.continuous)).subtype_mk _ }

def mappingPathRetraction {X Y : TopCat.{0}} (p : X ⟶ Y) : mappingPathSpace p ⟶ X :=
  TopCat.ofHom ⟨fun z => z.val.1, continuous_fst.comp continuous_subtype_val⟩

def mappingPathProjection {X Y : TopCat.{0}} (p : X ⟶ Y) : mappingPathSpace p ⟶ Y :=
  TopCat.ofHom ⟨fun z => z.val.2 1, by fun_prop⟩

@[reassoc]
theorem mappingPath_factorization {X Y : TopCat.{0}} (p : X ⟶ Y) :
    mappingPathInclusion p ≫ mappingPathProjection p = p := rfl

/-- Shrinking a path to its initial point leaves its point over `p` fixed. -/
def mappingPathContraction {X Y : TopCat.{0}} (p : X ⟶ Y) :
    ((mappingPathInclusion p).hom.comp (mappingPathRetraction p).hom).Homotopy
      (ContinuousMap.id (mappingPathSpace p)) where
  toFun z := ⟨(z.2.val.1, z.2.val.2.comp ⟨fun t => z.1 * t, by fun_prop⟩), by
    change z.2.val.2 (z.1 * 0) = p.hom z.2.val.1
    simpa using z.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × mappingPathSpace p) × unitInterval =>
      z.1.2.val.2 (z.1.1 * z.2))
    fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply ContinuousMap.ext
    intro t
    change z.val.2 (0 * t) = p.hom z.val.1
    simpa using z.property
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply ContinuousMap.ext
    intro t
    change z.val.2 (1 * t) = z.val.2 t
    rw [one_mul]

/-- The mapping-path inclusion is an actual homotopy equivalence. -/
def mappingPathEquiv {X Y : TopCat.{0}} (p : X ⟶ Y) :
    ContinuousMap.HomotopyEquiv X (mappingPathSpace p) where
  toFun := (mappingPathInclusion p).hom
  invFun := (mappingPathRetraction p).hom
  left_inv := ⟨ContinuousMap.Homotopy.refl _⟩
  right_inv := ⟨mappingPathContraction p⟩

theorem mappingPathProjection_weak_iff {X Y : TopCat.{0}} (p : X ⟶ Y) :
    IsWeakHomotopyEquivalence (mappingPathProjection p).hom ↔
      IsWeakHomotopyEquivalence p.hom := by
  change topologicalWeakEquivalences (mappingPathProjection p) ↔ topologicalWeakEquivalences p
  have hi : topologicalWeakEquivalences (mappingPathInclusion p) :=
    homotopyEquiv_isWeakHomotopyEquivalence (mappingPathEquiv p)
  constructor
  · intro h
    simpa only [mappingPath_factorization] using
      topologicalWeakEquivalences.comp_mem (mappingPathInclusion p) _ hi h
  · intro h
    apply topologicalWeakEquivalences.of_precomp (mappingPathInclusion p) _ hi
    simpa only [mappingPath_factorization] using h

end

end Thomason.Construction

end

section

/-! # Actual continuous homotopy fibres and their interpolation contraction -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- The homotopy fibre consists of a point and a path from its image to `b`. -/
def continuousHomotopyFiber {X Y : TopCat.{0}} (p : X ⟶ Y) (b : Y) : TopCat.{0} :=
  TopCat.of {z : mappingPathSpace p // (mappingPathProjection p).hom z = b}

def continuousHomotopyFiberRetraction {X Y : TopCat.{0}} (p : X ⟶ Y) (b : Y) :
    continuousHomotopyFiber p b ⟶ X :=
  TopCat.ofHom ⟨fun z => z.val.val.1, by fun_prop⟩

/-- A continuous interpolation provides a canonical path into the fibre. -/
def continuousHomotopyFiberSection {X Y : TopCat.{0}} (p : X ⟶ Y) (b : Y)
    (c : C(unitInterval × (Y × Y), Y))
    (h₀ : ∀ x y, c (0, x, y) = x) (h₁ : ∀ x y, c (1, x, y) = y) :
    X ⟶ continuousHomotopyFiber p b :=
  TopCat.ofHom {
    toFun x := ⟨⟨(x, ⟨fun t => c (t, p.hom x, b), by fun_prop⟩), h₀ _ _⟩, h₁ _ _⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply Continuous.prodMk continuous_id
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : X × unitInterval => c (z.2, p.hom z.1, b))
      fun_prop }

/-- Interpolation contracts each path to the canonical one, fixing both
endpoints. This uses an explicit diagonal-preserving interpolation, not a
homotopy-fibre preservation assumption. -/
def continuousHomotopyFiberContraction {X Y : TopCat.{0}} (p : X ⟶ Y) (b : Y)
    (c : C(unitInterval × (Y × Y), Y))
    (h₀ : ∀ x y, c (0, x, y) = x) (h₁ : ∀ x y, c (1, x, y) = y)
    (hd : ∀ t x, c (t, x, x) = x) :
    (ContinuousMap.id (continuousHomotopyFiber p b)).Homotopy
      ((continuousHomotopyFiberSection p b c h₀ h₁).hom.comp
        (continuousHomotopyFiberRetraction p b).hom) where
  toFun z := ⟨⟨(z.2.val.val.1, ⟨fun t =>
    c (z.1, z.2.val.val.2 t, c (t, p.hom z.2.val.val.1, b)), by fun_prop⟩), by
      change c (z.1, z.2.val.val.2 0, c (0, p.hom z.2.val.val.1, b)) = _
      rw [z.2.val.property, h₀, hd]⟩, by
      change c (z.1, z.2.val.val.2 1, c (1, p.hom z.2.val.val.1, b)) = b
      rw [show z.2.val.val.2 1 = b from z.2.property, h₁, hd]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × continuousHomotopyFiber p b) × unitInterval =>
      c (z.1.1, z.1.2.val.val.2 z.2, c (z.2, p.hom z.1.2.val.val.1, b)))
    fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply ContinuousMap.ext
    intro t
    exact h₀ _ _
  map_one_left z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply ContinuousMap.ext
    intro t
    exact h₁ _ _

/-- Over a continuously interpolated space the homotopy fibre projects by
an actual homotopy equivalence to the original source. -/
def continuousHomotopyFiberEquiv {X Y : TopCat.{0}} (p : X ⟶ Y) (b : Y)
    (c : C(unitInterval × (Y × Y), Y))
    (h₀ : ∀ x y, c (0, x, y) = x) (h₁ : ∀ x y, c (1, x, y) = y)
    (hd : ∀ t x, c (t, x, x) = x) :
    ContinuousMap.HomotopyEquiv (continuousHomotopyFiber p b) X where
  toFun := (continuousHomotopyFiberRetraction p b).hom
  invFun := (continuousHomotopyFiberSection p b c h₀ h₁).hom
  left_inv := ⟨(continuousHomotopyFiberContraction p b c h₀ h₁ hd).symm⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl _⟩

end

end Thomason.Construction

end

section

/-! # The actual functorial map between continuous homotopy fibres -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

def continuousHomotopyFiberMap {X X' Y Y' : TopCat.{0}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ p' = p ≫ g) (b : Y) :
    continuousHomotopyFiber p b ⟶ continuousHomotopyFiber p' (g.hom b) :=
  TopCat.ofHom {
    toFun z := ⟨⟨(f.hom z.val.val.1, g.hom.comp z.val.val.2), by
      change g.hom (z.val.val.2 0) = p'.hom (f.hom z.val.val.1)
      rw [z.val.property]
      exact (congrArg (fun k => k.hom z.val.val.1) h).symm⟩, by
      exact congrArg g.hom z.property⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply Continuous.prodMk (by fun_prop)
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : continuousHomotopyFiber p b × unitInterval =>
        g.hom (z.1.val.val.2 z.2))
      fun_prop }

@[reassoc]
theorem continuousHomotopyFiberMap_retraction {X X' Y Y' : TopCat.{0}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ p' = p ≫ g) (b : Y) :
    continuousHomotopyFiberMap p p' f g h b ≫
      continuousHomotopyFiberRetraction p' (g.hom b) =
        continuousHomotopyFiberRetraction p b ≫ f := rfl

/-- In a map of homotopy fibres, if both retractions and the source map are
weak equivalences, so is the original canonical fibre map. -/
theorem continuousHomotopyFiberMap_weak {X X' Y Y' : TopCat.{0}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ p' = p ≫ g) (b : Y)
    (hr : topologicalWeakEquivalences (continuousHomotopyFiberRetraction p b))
    (hr' : topologicalWeakEquivalences (continuousHomotopyFiberRetraction p' (g.hom b)))
    (hf : topologicalWeakEquivalences f) :
    topologicalWeakEquivalences (continuousHomotopyFiberMap p p' f g h b) := by
  apply topologicalWeakEquivalences.of_postcomp _ _ hr'
  rw [continuousHomotopyFiberMap_retraction]
  exact topologicalWeakEquivalences.comp_mem _ _ hr hf

end

end Thomason.Construction

end

section

/-! # Interpolation and actual homotopy fibres over finite cubes -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- Straight interpolation in the actual coordinates of a realized cube. -/
def pointInterpolation (n : ℕ) :
    C(unitInterval × (SSet.toTop.obj (obj n) × SSet.toTop.obj (obj n)),
      SSet.toTop.obj (obj n)) :=
  (sectionMap n).comp {
    toFun z j := ⟨(1 - (z.1 : ℝ)) * (coordinates n z.2.1 j : ℝ) +
        (z.1 : ℝ) * (coordinates n z.2.2 j : ℝ), by
      constructor
      · exact add_nonneg
          (mul_nonneg (sub_nonneg.mpr z.1.property.2) (coordinates n z.2.1 j).property.1)
          (mul_nonneg z.1.property.1 (coordinates n z.2.2 j).property.1)
      · have h₀ := (coordinates n z.2.1 j).property.2
        have h₁ := (coordinates n z.2.2 j).property.2
        have ht₀ := z.1.property.1
        have ht₁ := z.1.property.2
        nlinarith [mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr ht₁),
          mul_nonneg (sub_nonneg.mpr h₁) ht₀]⟩
    continuous_toFun := by
      apply continuous_pi
      intro j
      apply Continuous.subtype_mk
      fun_prop }

@[simp]
theorem pointInterpolation_zero (n : ℕ) (x y : SSet.toTop.obj (obj n)) :
    pointInterpolation n (0, x, y) = x := by
  change sectionMap n _ = x
  convert section_coordinates n x using 1
  apply congrArg (sectionMap n)
  funext j
  apply Subtype.ext
  simp

@[simp]
theorem pointInterpolation_one (n : ℕ) (x y : SSet.toTop.obj (obj n)) :
    pointInterpolation n (1, x, y) = y := by
  change sectionMap n _ = y
  convert section_coordinates n y using 1
  apply congrArg (sectionMap n)
  funext j
  apply Subtype.ext
  simp

@[simp]
theorem pointInterpolation_diagonal (n : ℕ) (t : unitInterval)
    (x : SSet.toTop.obj (obj n)) : pointInterpolation n (t, x, x) = x := by
  change sectionMap n _ = x
  convert section_coordinates n x using 1
  apply congrArg (sectionMap n)
  funext j
  apply Subtype.ext
  dsimp
  ring

/-- For every continuous map into the realized cube, its actual homotopy
fibre projects by a homotopy equivalence to its source. -/
def homotopyFiberEquiv {X : TopCat.{0}} (n : ℕ)
    (p : X ⟶ SSet.toTop.obj (obj n)) (b : SSet.toTop.obj (obj n)) :
    ContinuousMap.HomotopyEquiv (continuousHomotopyFiber p b) X :=
  continuousHomotopyFiberEquiv p b (pointInterpolation n)
    (pointInterpolation_zero n) (pointInterpolation_one n) (pointInterpolation_diagonal n)

end

end Thomason.Construction.RealizedCube

end

section

/-! # Exact compatibility of a lifted path with the actual homotopy fibre -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- The remaining part of an interval after time `s`, parametrized again
by the unit interval. -/
def remainingPathParameter (s t : unitInterval) : unitInterval :=
  unitInterval.symm (unitInterval.symm s * unitInterval.symm t)

@[simp] theorem remainingPathParameter_zero_right (s : unitInterval) :
    remainingPathParameter s 0 = s := by simp [remainingPathParameter]

@[simp] theorem remainingPathParameter_one_right (s : unitInterval) :
    remainingPathParameter s 1 = 1 := by simp [remainingPathParameter]

@[simp] theorem remainingPathParameter_zero_left (t : unitInterval) :
    remainingPathParameter 0 t = t := by simp [remainingPathParameter]

@[simp] theorem remainingPathParameter_one_left (t : unitInterval) :
    remainingPathParameter 1 t = 1 := by simp [remainingPathParameter]

/-- A family of points over the start of a path maps to its terminal
homotopy fibre by attaching that same path to every point. -/
def homotopyFiberFromPath {A E B : TopCat.{0}} (p : E ⟶ B) (f : A ⟶ E)
    {x y : B} (γ : Path x y) (hf : ∀ a, p.hom (f.hom a) = x) :
    A ⟶ continuousHomotopyFiber p y :=
  TopCat.ofHom {
    toFun a := ⟨⟨(f.hom a, γ.toContinuousMap), γ.source.trans (hf a).symm⟩, γ.target⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact f.hom.continuous.prodMk continuous_const }

/-- An actual lift of a base path gives an explicit homotopy in its terminal
homotopy fibre. The path coordinate is its remaining tail, so the statement
retains the whole family, not just its path components or weak status. -/
def homotopyFiberLiftedPath {A E B : TopCat.{0}} (p : E ⟶ B)
    {f g : A ⟶ E} (H : f.hom.Homotopy g.hom) {x y : B} (γ : Path x y)
    (hH : ∀ s a, p.hom (H (s,a)) = γ s) :
    (homotopyFiberFromPath p f γ
      (fun a => (congrArg p.hom (H.apply_zero a)).symm.trans ((hH 0 a).trans γ.source))).hom.Homotopy
    (homotopyFiberFromPath p g (Path.refl y)
      (fun a => (congrArg p.hom (H.apply_one a)).symm.trans ((hH 1 a).trans γ.target))).hom where
  toFun z := ⟨⟨(H z, ⟨fun t => γ (remainingPathParameter z.1 t), by
    apply γ.continuous.comp
    change Continuous (fun t : unitInterval =>
      unitInterval.symm (unitInterval.symm z.1 * unitInterval.symm t))
    fun_prop⟩), by
      change γ (remainingPathParameter z.1 0) = p.hom (H z)
      rw [remainingPathParameter_zero_right]
      exact (hH z.1 z.2).symm⟩, by
      change γ (remainingPathParameter z.1 1) = y
      rw [remainingPathParameter_one_right]
      exact γ.target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk H.continuous
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × A) × unitInterval =>
      γ (remainingPathParameter z.1.1 z.2))
    apply γ.continuous.comp
    change Continuous (fun z : (unitInterval × A) × unitInterval =>
      unitInterval.symm (unitInterval.symm z.1.1 * unitInterval.symm z.2))
    fun_prop
  map_zero_left a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact H.apply_zero a
    apply ContinuousMap.ext
    intro t
    exact congrArg γ (remainingPathParameter_zero_left t)
  map_one_left a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact H.apply_one a
    apply ContinuousMap.ext
    intro t
    exact (congrArg γ (remainingPathParameter_one_left t)).trans γ.target

/-- Consequently the two canonical maps into the actual homotopy fibre
have the same weak-equivalence status in every degree. -/
theorem homotopyFiberLiftedPath_weak_iff {A E B : TopCat.{0}} (p : E ⟶ B)
    {f g : A ⟶ E} (H : f.hom.Homotopy g.hom) {x y : B} (γ : Path x y)
    (hH : ∀ s a, p.hom (H (s,a)) = γ s) :
    topologicalWeakEquivalences (homotopyFiberFromPath p f γ
      (fun a => (congrArg p.hom (H.apply_zero a)).symm.trans ((hH 0 a).trans γ.source))) ↔
    topologicalWeakEquivalences (homotopyFiberFromPath p g (Path.refl y)
      (fun a => (congrArg p.hom (H.apply_one a)).symm.trans ((hH 1 a).trans γ.target))) :=
  isWeakHomotopyEquivalence_homotopy_iff (homotopyFiberLiftedPath p H γ hH)

end

end Thomason.Construction

end

section

/-! # Continuous path transport between actual homotopy fibres -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- The path coordinate of an actual homotopy-fibre point, with both
endpoints recorded in its type. -/
def homotopyFiberPath {E B : TopCat.{0}} {p : E ⟶ B} {b : B}
    (z : continuousHomotopyFiber p b) : Path (p.hom z.val.val.1) b where
  toContinuousMap := z.val.val.2
  source' := z.val.property
  target' := z.property

/-- Transport in the base appends the specified path and leaves the
point in the total space fixed. -/
def homotopyFiberPathTransport {E B : TopCat.{0}} (p : E ⟶ B) {b c : B}
    (γ : Path b c) : continuousHomotopyFiber p b ⟶ continuousHomotopyFiber p c :=
  TopCat.ofHom {
    toFun z := ⟨⟨(z.val.val.1, ((homotopyFiberPath z).trans γ).toContinuousMap),
      ((homotopyFiberPath z).trans γ).source⟩, ((homotopyFiberPath z).trans γ).target⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply Continuous.prodMk (by fun_prop)
      apply ContinuousMap.continuous_of_continuous_uncurry
      have hq : Continuous ↿(fun z : continuousHomotopyFiber p b => homotopyFiberPath z) := by
        change Continuous (fun z : continuousHomotopyFiber p b × unitInterval => z.1.val.val.2 z.2)
        fun_prop
      have hg : Continuous ↿(fun _ : continuousHomotopyFiber p b => γ) := by
        exact γ.continuous.comp continuous_snd
      exact Path.trans_continuous_family _ hq _ hg }

/-- Reparametrizing a homotopy-fibre path preserves its point coordinate. -/
def homotopyFiberReparametrize {E B : TopCat.{0}} (p : E ⟶ B) (b : B)
    (α : unitInterval → unitInterval) (hα : Continuous α) (h₀ : α 0 = 0) (h₁ : α 1 = 1) :
    continuousHomotopyFiber p b ⟶ continuousHomotopyFiber p b :=
  TopCat.ofHom {
    toFun z := ⟨⟨(z.val.val.1, ((homotopyFiberPath z).reparam α hα h₀ h₁).toContinuousMap),
      ((homotopyFiberPath z).reparam α hα h₀ h₁).source⟩,
      ((homotopyFiberPath z).reparam α hα h₀ h₁).target⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply Continuous.prodMk (by fun_prop)
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : continuousHomotopyFiber p b × unitInterval =>
        z.1.val.val.2 (α z.2))
      fun_prop }

/-- The reparametrization homotopy is continuous even as the starting
point of the path varies over the total space. -/
def homotopyFiberReparametrizeHomotopy {E B : TopCat.{0}} (p : E ⟶ B) (b : B)
    (α : unitInterval → unitInterval) (hα : Continuous α) (h₀ : α 0 = 0) (h₁ : α 1 = 1) :
    (ContinuousMap.id (continuousHomotopyFiber p b)).Homotopy
      (homotopyFiberReparametrize p b α hα h₀ h₁).hom where
  toFun z := ⟨⟨(z.2.val.val.1,
    ((Path.Homotopy.reparam (homotopyFiberPath z.2) α hα h₀ h₁).eval z.1).toContinuousMap),
    ((Path.Homotopy.reparam (homotopyFiberPath z.2) α hα h₀ h₁).eval z.1).source⟩,
    ((Path.Homotopy.reparam (homotopyFiberPath z.2) α hα h₀ h₁).eval z.1).target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × continuousHomotopyFiber p b) × unitInterval =>
      z.1.2.val.val.2 ⟨(unitInterval.symm z.1.1 : ℝ) * z.2 + z.1.1 * α z.2, _⟩)
    fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    exact congrArg Path.toContinuousMap (Path.Homotopy.eval_zero _)
  map_one_left z := by
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    exact congrArg Path.toContinuousMap (Path.Homotopy.eval_one _)

/-- A homotopy of base paths induces a homotopy of the actual transport
maps. All point coordinates remain fixed. -/
def homotopyFiberPathTransportHomotopy {E B : TopCat.{0}} (p : E ⟶ B) {b c : B}
    {γ δ : Path b c} (H : γ.Homotopy δ) :
    (homotopyFiberPathTransport p γ).hom.Homotopy (homotopyFiberPathTransport p δ).hom where
  toFun z := ⟨⟨(z.2.val.val.1, ((homotopyFiberPath z.2).trans (H.eval z.1)).toContinuousMap),
    ((homotopyFiberPath z.2).trans (H.eval z.1)).source⟩,
    ((homotopyFiberPath z.2).trans (H.eval z.1)).target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hq : Continuous ↿(fun z : unitInterval × continuousHomotopyFiber p b =>
        homotopyFiberPath z.2) := by
      change Continuous (fun z : (unitInterval × continuousHomotopyFiber p b) × unitInterval =>
        z.1.2.val.val.2 z.2)
      fun_prop
    exact Path.trans_continuous_family _ hq
      (fun z : unitInterval × continuousHomotopyFiber p b => H.eval z.1) (by
        change Continuous (fun z : (unitInterval × continuousHomotopyFiber p b) × unitInterval =>
          H (z.1.1, z.2))
        fun_prop)
  map_zero_left z := by
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    exact congrArg (fun q => ((homotopyFiberPath z).trans q).toContinuousMap) (H.eval_zero)
  map_one_left z := by
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    exact congrArg (fun q => ((homotopyFiberPath z).trans q).toContinuousMap) (H.eval_one)

/-- Associating the appended paths is a homotopy on the whole homotopy
fibre, including the varying point and starting endpoint. -/
def homotopyFiberPathTransportAssoc {E B : TopCat.{0}} (p : E ⟶ B) {b c d : B}
    (γ : Path b c) (δ : Path c d) :
    (homotopyFiberPathTransport p γ ≫ homotopyFiberPathTransport p δ).hom.Homotopy
      (homotopyFiberPathTransport p (γ.trans δ)).hom := by
  let H := (homotopyFiberReparametrizeHomotopy p d
    PathSpace.associatingParameter PathSpace.associatingParameter_continuous
    PathSpace.associatingParameter_zero PathSpace.associatingParameter_one).compContinuousMap
      (homotopyFiberPathTransport p (γ.trans δ)).hom
  refine H.symm.cast ?_ rfl
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Subtype.ext
  refine Prod.ext (by rfl) ?_
  exact congrArg Path.toContinuousMap
    (Path.Homotopy.trans_assoc_reparam (homotopyFiberPath z) γ δ).symm

end

end Thomason.Construction

end

section

/-! # Transport between actual homotopy fibres is a homotopy equivalence -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

private def fibreRightUnitParameter (t : unitInterval) : unitInterval :=
  ⟨Path.Homotopy.transReflReparamAux t, Path.Homotopy.transReflReparamAux_mem_I t⟩

/-- Appending the constant path is homotopic to the identity, continuously
in every total-space point and every homotopy-fibre path. -/
def homotopyFiberPathTransportUnit {E B : TopCat.{0}} (p : E ⟶ B) (b : B) :
    (homotopyFiberPathTransport p (Path.refl b)).hom.Homotopy
      (ContinuousMap.id (continuousHomotopyFiber p b)) := by
  let H := homotopyFiberReparametrizeHomotopy p b fibreRightUnitParameter
    (Path.Homotopy.continuous_transReflReparamAux.subtype_mk _)
    (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
    (Subtype.ext Path.Homotopy.transReflReparamAux_one)
  refine H.symm.cast ?_ rfl
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Subtype.ext
  refine Prod.ext (by rfl) ?_
  exact congrArg Path.toContinuousMap (Path.Homotopy.trans_refl_reparam (homotopyFiberPath z)).symm

/-- A path followed by its reverse cancels on the full actual homotopy
fibre. This is stronger than equality on components. -/
def homotopyFiberPathTransportCancel {E B : TopCat.{0}} (p : E ⟶ B) {b c : B}
    (γ : Path b c) :
    (homotopyFiberPathTransport p γ ≫ homotopyFiberPathTransport p γ.symm).hom.Homotopy
      (ContinuousMap.id (continuousHomotopyFiber p b)) :=
  (homotopyFiberPathTransportAssoc p γ γ.symm).trans
    ((homotopyFiberPathTransportHomotopy p (Path.Homotopy.reflTransSymm γ).symm).trans
      (homotopyFiberPathTransportUnit p b))

/-- The explicit homotopy equivalence between homotopy fibres associated
to a base path; its inverse appends the reversed path. -/
def homotopyFiberPathEquiv {E B : TopCat.{0}} (p : E ⟶ B) {b c : B} (γ : Path b c) :
    ContinuousMap.HomotopyEquiv (continuousHomotopyFiber p b) (continuousHomotopyFiber p c) where
  toFun := (homotopyFiberPathTransport p γ).hom
  invFun := (homotopyFiberPathTransport p γ.symm).hom
  left_inv := ⟨homotopyFiberPathTransportCancel p γ⟩
  right_inv := ⟨by
    have H := homotopyFiberPathTransportCancel p γ.symm
    rw [Path.symm_symm] at H
    exact H.cast rfl rfl⟩

/-- Base-path transport on the actual homotopy fibres is an actual weak
homotopy equivalence, independently of all simplicial model inputs. -/
theorem homotopyFiberPathTransport_weak {E B : TopCat.{0}} (p : E ⟶ B)
    {b c : B} (γ : Path b c) :
    topologicalWeakEquivalences (homotopyFiberPathTransport p γ) :=
  homotopyEquiv_isWeakHomotopyEquivalence (homotopyFiberPathEquiv p γ)

end

end Thomason.Construction

end

end OAI
