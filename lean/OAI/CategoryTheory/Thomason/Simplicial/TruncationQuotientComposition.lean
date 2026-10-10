import OAI.CategoryTheory.Thomason.Gray.TopologicalIntervalCylinder
import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Simplicial.RealizedSimplexWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import Mathlib.Topology.Category.TopCat.Monoidal

namespace OAI

section

/-! # Normalizing generated expressions at a fixed composition level

An essential expression whose compositions occur at levels at most r
is an actual r-string with exactly one generator above r in every factor.
The length equals the number of higher generator occurrences. Endpoint
expressions are supplied by dimensionwise composition generation.
-/

namespace Thomason.Construction.StrictOmegaCategory

open ExpressionDegree

variable {C : StrictOmegaCategory.{0}} {I : Type} {g : I → C} {d : I → ℕ}

/-- The exact dimensionwise generation hypothesis used in Steiner's
normalization argument. It follows from `exists_bounded_expression` for
the positive-table comparisons. -/
def DimensionwiseGenerated (C : StrictOmegaCategory.{0}) {I : Type}
    (g : I → C) (d : I → ℕ) : Prop :=
  ∀ n x, C.DimensionLE n x →
    ∃ t : CompositionExpression C g x, ∀ i ∈ t.labels, d i ≤ n

namespace EssentialExpression

theorem highGeneratorString (hg : ∀ i, C.DimensionLE (d i) (g i))
    (hgen : DimensionwiseGenerated C g d) {x : C}
    (t : EssentialExpression C g x) (r : ℕ) (hlevels : t.levelsLE r)
    (hcount : 0 < highCount d r t.expression.labels) :
    HighGeneratorString C g d r x (highCount d r t.expression.labels) := by
  induction t with
  | generator i =>
    have hi : r < d i := by
      by_contra hi
      simp [expression, CompositionExpression.labels, highCount, hi] at hcount
    have he : highCount d r
        (CompositionExpression.generator (C := C) (g := g) i).labels = 1 := by
      simp [CompositionExpression.labels, highCount, hi]
    simpa only [expression, he] using HighGeneratorString.singleton
      (CompositionExpression.generator (C := C) (g := g) i) he
  | @comp x y s hxy tx ty hx hy ihx ihy =>
    have hs : s ≤ r := hlevels.1
    have hsum : highCount d r
        (EssentialExpression.comp s hxy tx ty hx hy).expression.labels =
        highCount d r tx.expression.labels + highCount d r ty.expression.labels := by
      simp only [expression, CompositionExpression.labels, highCount_append]
    by_cases hcx : highCount d r tx.expression.labels = 0
    · have hdy : 0 < highCount d r ty.expression.labels := by
        rw [hsum, hcx, Nat.zero_add] at hcount
        exact hcount
      have hxr : C.DimensionLE r x := tx.expression.dimensionLE d hg r
        ((highCount_eq_zero_iff d r tx.expression.labels).mp hcx)
      have hys := ihy hlevels.2.2 hdy
      rw [hsum, hcx, Nat.zero_add]
      by_cases hsr : s = r
      · subst s
        rw [C.comp_of_dimensionLE (Nat.le_refl r) hxr hxy]
        exact hys
      · exact hys.whisker_left tx.expression hcx hxr (by omega) hxy
    · have hdx : 0 < highCount d r tx.expression.labels := Nat.pos_of_ne_zero hcx
      have hxs := ihx hlevels.2.1 hdx
      by_cases hcy : highCount d r ty.expression.labels = 0
      · have hyr : C.DimensionLE r y := ty.expression.dimensionLE d hg r
          ((highCount_eq_zero_iff d r ty.expression.labels).mp hcy)
        rw [hsum, hcy, Nat.add_zero]
        by_cases hsr : s = r
        · subst s
          rw [comp_eq_left_of_dimensionLE r hxy hyr]
          exact hxs
        · exact hxs.whisker_right ty.expression hcy hyr (by omega) hxy
      · have hdy : 0 < highCount d r ty.expression.labels := Nat.pos_of_ne_zero hcy
        have hys := ihy hlevels.2.2 hdy
        rw [hsum]
        by_cases hsr : s = r
        · subst s
          exact hxs.append hys hxy
        · have hsr' : s < r := by omega
          obtain ⟨ts, hts⟩ := hgen r (C.source r y) (C.face_dimensionLE false r y)
          obtain ⟨tt, htt⟩ := hgen r (C.target r x) (C.face_dimensionLE true r x)
          have hts0 := (highCount_eq_zero_iff d r ts.labels).mpr hts
          have htt0 := (highCount_eq_zero_iff d r tt.labels).mpr htt
          have hl := hxs.whisker_right ts hts0 (C.face_dimensionLE false r y) hsr'
            (C.matching_face_right hsr' x y hxy false)
          have hr := hys.whisker_left tt htt0 (C.face_dimensionLE true r x) hsr'
            (C.matching_face_left hsr' x y hxy true)
          have hh := hl.append hr (C.whiskered_forward_matching hsr' x y hxy)
          change HighGeneratorString C g d r
            (C.comp r (C.rightWhisker hsr' x y hxy false)
              (C.leftWhisker hsr' x y hxy true)
              (C.whiskered_forward_matching hsr' x y hxy)) _ at hh
          rw [C.whiskered_forward_comp] at hh
          exact hh

end EssentialExpression

/-- The fixed-level form of the generated-expression normalization
theorem. Every factor retains its actual expression and has exactly one
higher generator. -/
theorem exists_normalized_generator_string
    (hg : ∀ i, C.DimensionLE (d i) (g i))
    (hgen : DimensionwiseGenerated C g d) {x : C}
    (t : EssentialExpression C g x) (r : ℕ) (hlevels : t.levelsLE r)
    (hcount : 0 < highCount d r t.expression.labels) :
    ∃ xs : List C, xs.length = highCount d r t.expression.labels ∧
      CompositeList C r xs x ∧
      ∀ y ∈ xs, ∃ e : CompositionExpression C g y, highCount d r e.labels = 1 :=
  (t.highGeneratorString hg hgen r hlevels hcount).exists_list

/-- Every generated cell is either one of the chosen generators or a
nontrivial string whose factors each contain exactly one higher generator. -/
theorem generator_or_normalized_string
    (hg : ∀ i, C.DimensionLE (d i) (g i))
    (hgen : DimensionwiseGenerated C g d) {x : C}
    (t : CompositionExpression C g x) :
    (∃ i, x = g i) ∨ ∃ (r : ℕ) (xs : List C), 2 ≤ xs.length ∧
      CompositeList C r xs x ∧
      ∀ y ∈ xs, ∃ e : CompositionExpression C g y, highCount d r e.labels = 1 := by
  obtain ⟨s⟩ := t.exists_essential
  rcases s.generator_or_critical d hg with h | ⟨r, hc, _, hlevels⟩
  · exact Or.inl h
  · obtain ⟨xs, hlen, hxs, hprop⟩ := exists_normalized_generator_string hg hgen s r
      hlevels (by omega)
    exact Or.inr ⟨r, xs, by omega, hxs, hprop⟩

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Homotopy invariance from basepoint invariance in one fixed degree

These lemmas isolate the induction step's topology. A path comparison in a
single positive degree implies homotopy invariance and the homotopy-equivalence
test in that degree, using the explicitly proved weak interval sections.
-/

namespace Thomason.Construction.HomotopyMaps

universe u

/-- Bijectivity is unchanged along a path of source basepoints in this degree. -/
def BasepointInvariant (n : ℕ) : Prop :=
  ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x y : X}, Path x y →
    (Function.Bijective (groupMap f (n+1) x) ↔ Function.Bijective (groupMap f (n+1) y))

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Moving the source basepoint along the cylinder proves unbased homotopy
invariance of the bijectivity test, in the specified degree. -/
theorem homotopy_bijective_iff_of_basepoint {n : ℕ} (h : BasepointInvariant.{u} n)
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X) :
    Function.Bijective (groupMap f (n+1) x) ↔ Function.Bijective (groupMap g (n+1) x) := by
  let F : C(X × unitInterval, Y) := H.toContinuousMap.comp ⟨Prod.swap, by fun_prop⟩
  let s₀ : C(X, X × unitInterval) := ⟨fun a => (a, 0), by fun_prop⟩
  let s₁ : C(X, X × unitInterval) := ⟨fun a => (a, 1), by fun_prop⟩
  have hz : F.comp s₀ = f := by
    apply ContinuousMap.ext
    intro a
    exact H.apply_zero a
  have ho : F.comp s₁ = g := by
    apply ContinuousMap.ext
    intro a
    exact H.apply_one a
  let p : Path (s₀ x) (s₁ x) := ⟨⟨fun t => (x, t), by fun_prop⟩, rfl, rfl⟩
  have hs₀ : Function.Bijective (groupMap s₀ (n+1) x) :=
    (TopologicalInterval.section_weak (TopCat.of X) 0).2 n x
  have hs₁ : Function.Bijective (groupMap s₁ (n+1) x) :=
    (TopologicalInterval.section_weak (TopCat.of X) 1).2 n x
  calc
    _ ↔ Function.Bijective (groupMap (F.comp s₀) (n+1) x) := by rw [hz]
    _ ↔ Function.Bijective (groupMap F (n+1) (s₀ x)) := by
      rw [groupMap_comp s₀ F]
      exact hs₀.of_comp_iff _
    _ ↔ Function.Bijective (groupMap F (n+1) (s₁ x)) := h F p
    _ ↔ Function.Bijective (groupMap (F.comp s₁) (n+1) x) := by
      rw [groupMap_comp s₁ F]
      exact (hs₁.of_comp_iff _).symm
    _ ↔ _ := by rw [ho]

/-- A homotopy equivalence induces a bijection in the specified degree once
basepoint invariance is known in that degree. -/
theorem homotopyEquiv_bijective_of_basepoint {n : ℕ} (h : BasepointInvariant.{u} n)
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Function.Bijective (groupMap e.toFun (n+1) x) := by
  let H := e.left_inv.some
  have hl (a : X) : Function.Bijective (groupMap (e.invFun.comp e.toFun) (n+1) a) :=
    (homotopy_bijective_iff_of_basepoint h H a).mpr (by
      rw [groupMap_id]
      exact Function.bijective_id)
  have hr (b : Y) : Function.Bijective (groupMap (e.toFun.comp e.invFun) (n+1) b) :=
    (homotopy_bijective_iff_of_basepoint h e.right_inv.some b).mpr (by
      rw [groupMap_id]
      exact Function.bijective_id)
  have hinj (a : X) : Function.Injective (groupMap e.toFun (n+1) a) := by
    intro q r he
    apply (hl a).1
    rw [groupMap_comp]
    exact congrArg (groupMap e.invFun (n+1) (e.toFun a)) he
  have hs : Function.Surjective (groupMap e.toFun (n+1) (e.invFun (e.toFun x))) := by
    intro q
    obtain ⟨r, hr⟩ := (hr (e.toFun x)).2 q
    rw [groupMap_comp] at hr
    exact ⟨groupMap e.invFun (n+1) (e.toFun x) r, hr⟩
  let p : Path (e.invFun (e.toFun x)) x :=
    ⟨⟨fun t => H (t, x), H.continuous.comp (by fun_prop)⟩,
      H.apply_zero x, H.apply_one x⟩
  exact (h e.toFun p).mp ⟨hinj _, hs⟩

end Thomason.Construction.HomotopyMaps

end

section

/-! # Basepoint invariance of all actual homotopy-group bijectivity tests

The induction starts with fundamental-group conjugation. The step uses the
proved natural cubical dimension shift and continuous loop-space conjugation.
-/

namespace Thomason.Construction.HomotopyMaps

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The natural dimension shift preserves exactly the bijectivity test. -/
theorem loopDimensionShift_bijective_iff (f : C(X, Y)) (n : ℕ) (x : X) :
    Function.Bijective (groupMap f (n+1) x) ↔
      Function.Bijective (groupMap (PathSpace.map f) n (Path.refl x)) := by
  have he : loopDimensionShift n (f x) ∘ groupMap f (n+1) x =
      basedGroupMap (PathSpace.map f)
        (show PathSpace.map f (Path.refl x) = Path.refl (f x) from rfl) n ∘
          loopDimensionShift n x := by
    funext p
    exact loopDimensionShift_naturality f n x p
  rw [← basedGroupMap_bijective_iff (PathSpace.map f)
    (show PathSpace.map f (Path.refl x) = Path.refl (f x) from rfl) n]
  rw [← (loopDimensionShift n x).bijective.of_comp_iff, ← he,
    (loopDimensionShift n (f x)).bijective.of_comp_iff']

/-- Passing to path spaces advances basepoint invariance by one degree. -/
theorem basepointInvariant_succ {n : ℕ} (h : BasepointInvariant.{u} n) :
    BasepointInvariant.{u} (n+1) := by
  intro X Y _ _ f x y p
  have hx : Function.Bijective
      (groupMap (PathSpace.conjugate p) (n+1) (Path.refl x)) := by
    simpa only [PathSpace.conjugateEquiv_toFun] using
      homotopyEquiv_bijective_of_basepoint h (PathSpace.conjugateEquiv p) (Path.refl x)
  have hy : Function.Bijective
      (groupMap (PathSpace.conjugate (p.map f.continuous)) (n+1) (Path.refl (f x))) := by
    simpa only [PathSpace.conjugateEquiv_toFun] using
      homotopyEquiv_bijective_of_basepoint h (PathSpace.conjugateEquiv (p.map f.continuous))
        (Path.refl (f x))
  calc
    _ ↔ Function.Bijective (groupMap (PathSpace.map f) (n+1) (Path.refl x)) :=
      loopDimensionShift_bijective_iff f (n+1) x
    _ ↔ Function.Bijective (groupMap
        ((PathSpace.conjugate (p.map f.continuous)).comp (PathSpace.map f))
          (n+1) (Path.refl x)) := by
      rw [groupMap_comp]
      exact (hy.of_comp_iff' _).symm
    _ ↔ Function.Bijective (groupMap
        ((PathSpace.map f).comp (PathSpace.conjugate p)) (n+1) (Path.refl x)) := by
      rw [PathSpace.conjugate_naturality]
    _ ↔ Function.Bijective (groupMap (PathSpace.map f) (n+1)
        (PathSpace.conjugate p (Path.refl x))) := by
      rw [groupMap_comp]
      exact hx.of_comp_iff _
    _ ↔ Function.Bijective (groupMap (PathSpace.map f) (n+1) (Path.refl y)) :=
      h (PathSpace.map f) (PathSpace.conjugateConstantPath p)
    _ ↔ _ := (loopDimensionShift_bijective_iff f (n+1) y).symm

/-- Bijectivity in every positive degree depends only on the source path component. -/
theorem groupMap_bijective_path (n : ℕ) : BasepointInvariant.{u} n := by
  induction n with
  | zero =>
    intro X Y _ _ f x y p
    exact groupMap_one_bijective_iff f p
  | succ n h => exact basepointInvariant_succ h

end Thomason.Construction.HomotopyMaps

end

section

/-! # Unconditional two-out-of-three for realization weak equivalences

Source cancellation uses component surjectivity and the proved invariance
of every homotopy-group bijectivity test along a path. The weak-equivalence
class remains the actual geometric-realization definition.
-/

namespace Thomason.Construction

open CategoryTheory

universe u

namespace IsWeakHomotopyEquivalence

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] {f : C(X, Y)} {g : C(Y, Z)}

/-- A weak precomposition can be cancelled without pointwise surjectivity. -/
theorem of_precomp (hf : IsWeakHomotopyEquivalence f)
    (hfg : IsWeakHomotopyEquivalence (g.comp f)) : IsWeakHomotopyEquivalence g := by
  constructor
  · apply (hf.1.of_comp_iff _).mp
    simpa only [HomotopyMaps.componentsMap_comp] using hfg.1
  · intro n y
    obtain ⟨c, hc⟩ := hf.1.2 (ZerothHomotopy.mk y)
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
    obtain ⟨p⟩ : Joined (f x) y := Quotient.exact hc
    have hb : Function.Bijective (HomotopyMaps.groupMap g (n+1) (f x)) := by
      apply ((hf.2 n x).of_comp_iff _).mp
      simpa only [HomotopyMaps.groupMap_comp] using hfg.2 n x
    exact (HomotopyMaps.groupMap_bijective_path n g p).mp hb

end IsWeakHomotopyEquivalence

instance : topologicalWeakEquivalences.{u}.HasOfPrecompProperty
    topologicalWeakEquivalences.{u} where
  of_precomp _ _ hf hfg := IsWeakHomotopyEquivalence.of_precomp hf hfg

instance : topologicalWeakEquivalences.{u}.HasTwoOutOfThreeProperty where
  toIsStableUnderComposition := inferInstance
  toHasOfPostcompProperty := inferInstance
  toHasOfPrecompProperty := inferInstance

instance : realizationWeakEquivalences.{u}.HasOfPrecompProperty
    realizationWeakEquivalences.{u} where
  of_precomp f g hf hfg := by
    apply topologicalWeakEquivalences.of_precomp (SSet.toTop.map f) (SSet.toTop.map g) hf
    change topologicalWeakEquivalences (SSet.toTop.map (f ≫ g)) at hfg
    simpa only [Functor.map_comp] using hfg

instance : realizationWeakEquivalences.{u}.HasTwoOutOfThreeProperty where
  toIsStableUnderComposition := inferInstance
  toHasOfPostcompProperty := inferInstance
  toHasOfPrecompProperty := inferInstance

end Thomason.Construction

end

section

/-! # Boundary-lifting weak equivalences from cylinder endpoints

The geometric input is isolated to the two endpoint inclusions. The section,
homotopy and arrow retract are all constructed explicitly.
-/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

universe u

/-- Two weak endpoint inclusions suffice for homotopy invariance on that source. -/
theorem simplicialHomotopy_weak_iff_of_endpoints {X Y : SSet.{u}} {f g : X ⟶ Y}
    (h₀ : realizationWeakEquivalences (SSet.ι₀ (X := X)))
    (h₁ : realizationWeakEquivalences (SSet.ι₁ (X := X))) (H : SSet.Homotopy f g) :
    realizationWeakEquivalences f ↔ realizationWeakEquivalences g := by
  constructor
  · intro hf
    have hH : realizationWeakEquivalences H.h := by
      apply realizationWeakEquivalences.of_precomp SSet.ι₀ H.h h₀
      rwa [H.h₀]
    simpa only [H.h₁] using realizationWeakEquivalences.comp_mem _ _ h₁ hH
  · intro hg
    have hH : realizationWeakEquivalences H.h := by
      apply realizationWeakEquivalences.of_precomp SSet.ι₁ H.h h₁
      rwa [H.h₁]
    simpa only [H.h₀] using realizationWeakEquivalences.comp_mem _ _ h₀ hH

/-- Explicit retraction data and weak endpoints imply the map is weak. -/
theorem BoundaryRetraction.weakEquivalence {X Y : SSet.{u}} {f : X ⟶ Y}
    (d : BoundaryRetraction f)
    (h₀ : realizationWeakEquivalences (SSet.ι₀ (X := X)))
    (h₁ : realizationWeakEquivalences (SSet.ι₁ (X := X))) :
    realizationWeakEquivalences f := by
  have hw : realizationWeakEquivalences (f ≫ d.section_) :=
    (simplicialHomotopy_weak_iff_of_endpoints h₀ h₁ d.homotopy).mpr
      (realizationWeakEquivalences.id_mem X)
  let r : RetractArrow f (f ≫ d.section_) := {
    i := Arrow.homMk (𝟙 X) d.section_ (by simp)
    r := Arrow.homMk (𝟙 X) f (by simp [Category.assoc, d.section_comp])
    retract := by
      apply Arrow.hom_ext
      · simp
      · exact d.section_comp }
  exact realizationWeakEquivalences.of_retract r hw

/-- Boundary lifting satisfies the actual weak test as soon as the two
cylinder endpoints do; no model structure is assumed. -/
theorem boundary_rlp_weak_of_endpoints {X Y : SSet.{u}} (f : X ⟶ Y) (hf : I.rlp f)
    (h₀ : realizationWeakEquivalences (SSet.ι₀ (X := X)))
    (h₁ : realizationWeakEquivalences (SSet.ι₁ (X := X))) :
    realizationWeakEquivalences f :=
  (boundaryRetraction f hf).weakEquivalence h₀ h₁

end Thomason.Construction

end

section

/-! # Two out of six for actual weak homotopy equivalences -/

namespace Thomason.Construction

open CategoryTheory

universe u

namespace IsWeakHomotopyEquivalence

/-- If the two overlapping composites are weak, then the middle map is
weak. Surjectivity on components brings every base point into the image
where the two given homotopy-group tests apply. -/
theorem middle_of_two_composites {X Y Z T : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]
    (f : C(X, Y)) (g : C(Y, Z)) (h : C(Z, T))
    (hfg : IsWeakHomotopyEquivalence (g.comp f))
    (hgh : IsWeakHomotopyEquivalence (h.comp g)) :
    IsWeakHomotopyEquivalence g := by
  have hfg₀ : Function.Bijective (HomotopyMaps.componentsMap g ∘ HomotopyMaps.componentsMap f) := by
    simpa only [HomotopyMaps.componentsMap_comp] using hfg.1
  have hgh₀ : Function.Bijective (HomotopyMaps.componentsMap h ∘ HomotopyMaps.componentsMap g) := by
    simpa only [HomotopyMaps.componentsMap_comp] using hgh.1
  have hg₀ : Function.Bijective (HomotopyMaps.componentsMap g) := by
    constructor
    · intro x y he
      exact hgh₀.1 (congrArg (HomotopyMaps.componentsMap h) he)
    · intro z
      obtain ⟨x, hx⟩ := hfg₀.2 z
      exact ⟨HomotopyMaps.componentsMap f x, hx⟩
  have hf₀ : Function.Surjective (HomotopyMaps.componentsMap f) := by
    intro y
    obtain ⟨x, hx⟩ := hfg₀.2 (HomotopyMaps.componentsMap g y)
    exact ⟨x, hg₀.1 hx⟩
  refine ⟨hg₀, ?_⟩
  intro n y
  obtain ⟨c, hc⟩ := hf₀ (ZerothHomotopy.mk y)
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  obtain ⟨p⟩ : Joined (f x) y := Quotient.exact hc
  apply (HomotopyMaps.groupMap_bijective_path n g p).mp
  have hfg' : Function.Bijective
      (HomotopyMaps.groupMap g (n+1) (f x) ∘ HomotopyMaps.groupMap f (n+1) x) := by
    simpa only [HomotopyMaps.groupMap_comp] using hfg.2 n x
  have hgh' : Function.Bijective
      (HomotopyMaps.groupMap h (n+1) (g (f x)) ∘ HomotopyMaps.groupMap g (n+1) (f x)) := by
    simpa only [HomotopyMaps.groupMap_comp] using hgh.2 n (f x)
  constructor
  · intro a b he
    exact hgh'.1 (congrArg (HomotopyMaps.groupMap h (n+1) (g (f x))) he)
  · intro z
    obtain ⟨a, ha⟩ := hfg'.2 z
    exact ⟨HomotopyMaps.groupMap f (n+1) x a, ha⟩

end IsWeakHomotopyEquivalence

/-- Two overlapping weak composites force all three maps, and their full
composite, to be actual topological weak equivalences. -/
theorem topologicalWeakEquivalences_two_out_of_six {A B C D : TopCat.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (hab : topologicalWeakEquivalences (a ≫ b))
    (hbc : topologicalWeakEquivalences (b ≫ c)) :
    topologicalWeakEquivalences a ∧ topologicalWeakEquivalences b ∧
      topologicalWeakEquivalences c ∧ topologicalWeakEquivalences (a ≫ b ≫ c) := by
  have hb : topologicalWeakEquivalences b :=
    IsWeakHomotopyEquivalence.middle_of_two_composites a.hom b.hom c.hom hab hbc
  have ha := topologicalWeakEquivalences.of_postcomp a b hb hab
  have hc := topologicalWeakEquivalences.of_precomp b c hb hbc
  exact ⟨ha, hb, hc, topologicalWeakEquivalences.comp_mem _ _ ha hbc⟩

/-- The same saturated cancellation applies to the actual realization
weak-equivalence class, with no Kan--Quillen hypothesis. -/
theorem realizationWeakEquivalences_two_out_of_six {A B C D : SSet.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (hab : realizationWeakEquivalences (a ≫ b))
    (hbc : realizationWeakEquivalences (b ≫ c)) :
    realizationWeakEquivalences a ∧ realizationWeakEquivalences b ∧
      realizationWeakEquivalences c ∧ realizationWeakEquivalences (a ≫ b ≫ c) := by
  have hab' : topologicalWeakEquivalences (SSet.toTop.map a ≫ SSet.toTop.map b) := by
    change topologicalWeakEquivalences (SSet.toTop.map (a ≫ b)) at hab
    simpa only [SSet.toTop.map_comp] using hab
  have hbc' : topologicalWeakEquivalences (SSet.toTop.map b ≫ SSet.toTop.map c) := by
    change topologicalWeakEquivalences (SSet.toTop.map (b ≫ c)) at hbc
    simpa only [SSet.toTop.map_comp] using hbc
  obtain ⟨ha, hb, hc, _⟩ := topologicalWeakEquivalences_two_out_of_six
    (SSet.toTop.map a) (SSet.toTop.map b) (SSet.toTop.map c) hab' hbc'
  exact ⟨ha, hb, hc, realizationWeakEquivalences.comp_mem _ _ ha hbc⟩

end Thomason.Construction

end

section

/-! # Homotopy equivalences and homotopies satisfy the semantic weak test

This proof is independent of Kan–Quillen factorization systems.
-/

namespace Thomason.Construction

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- An actual topological homotopy equivalence is a weak homotopy equivalence. -/
theorem homotopyEquiv_isWeakHomotopyEquivalence (e : ContinuousMap.HomotopyEquiv X Y) :
    IsWeakHomotopyEquivalence e.toFun := by
  constructor
  · have hl : HomotopyMaps.componentsMap e.invFun ∘ HomotopyMaps.componentsMap e.toFun = id := by
      rw [← HomotopyMaps.componentsMap_comp,
        HomotopyMaps.componentsMap_homotopy e.left_inv.some, HomotopyMaps.componentsMap_id]
    have hr : HomotopyMaps.componentsMap e.toFun ∘ HomotopyMaps.componentsMap e.invFun = id := by
      rw [← HomotopyMaps.componentsMap_comp,
        HomotopyMaps.componentsMap_homotopy e.right_inv.some, HomotopyMaps.componentsMap_id]
    exact ⟨(show Function.LeftInverse (HomotopyMaps.componentsMap e.invFun)
      (HomotopyMaps.componentsMap e.toFun) from congrFun hl).injective,
      (show Function.RightInverse (HomotopyMaps.componentsMap e.invFun)
      (HomotopyMaps.componentsMap e.toFun) from congrFun hr).surjective⟩
  · intro n x
    exact HomotopyMaps.homotopyEquiv_bijective_of_basepoint
      (HomotopyMaps.groupMap_bijective_path n) e x

/-- Unbased homotopies preserve the full semantic weak-equivalence test. -/
theorem isWeakHomotopyEquivalence_homotopy_iff {f g : C(X, Y)} (H : f.Homotopy g) :
    IsWeakHomotopyEquivalence f ↔ IsWeakHomotopyEquivalence g := by
  unfold IsWeakHomotopyEquivalence
  apply and_congr
  · rw [HomotopyMaps.componentsMap_homotopy H]
  · exact forall_congr' (fun n => forall_congr' (fun x =>
      HomotopyMaps.homotopy_bijective_iff_of_basepoint
        (HomotopyMaps.groupMap_bijective_path n) H x))

/-- Loop-space conjugation is weak in the actual all-degree sense. -/
theorem pathConjugation_isWeakHomotopyEquivalence {x y : X} (p : Path x y) :
    IsWeakHomotopyEquivalence (PathSpace.conjugate p) :=
  homotopyEquiv_isWeakHomotopyEquivalence (PathSpace.conjugateEquiv p)

end Thomason.Construction

end

section

/-! # Surjectivity on homotopy groups is independent of the source basepoint -/

namespace Thomason.Construction.HomotopyMaps

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem loopDimensionShift_surjective_iff (f : C(X, Y)) (n : ℕ) (x : X) :
    Function.Surjective (groupMap f (n+1) x) ↔
      Function.Surjective (groupMap (PathSpace.map f) n (Path.refl x)) := by
  have he : loopDimensionShift n (f x) ∘ groupMap f (n+1) x =
      basedGroupMap (PathSpace.map f)
        (show PathSpace.map f (Path.refl x) = Path.refl (f x) from rfl) n ∘
          loopDimensionShift n x := by
    funext p
    exact loopDimensionShift_naturality f n x p
  rw [← Function.Surjective.of_comp_iff' (loopDimensionShift n (f x)).bijective
    (groupMap f (n+1) x), he,
    Function.Surjective.of_comp_iff _ (loopDimensionShift n x).surjective]
  rfl

theorem groupMap_one_surjective_path (f : C(X, Y)) {x y : X} (p : Path x y) :
    Function.Surjective (groupMap f 1 x) ↔ Function.Surjective (groupMap f 1 y) := by
  have he : groupMap f 1 y ∘ piOneTransport p =
      piOneTransport (p.map f.continuous) ∘ groupMap f 1 x := by
    funext q
    exact piOneTransport_naturality f p q
  rw [← Function.Surjective.of_comp_iff' (piOneTransport (p.map f.continuous)).bijective
    (groupMap f 1 x), ← he,
    Function.Surjective.of_comp_iff _ (piOneTransport p).surjective]

private def SurjectiveBasepointInvariant (n : ℕ) : Prop :=
  ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x y : X}, Path x y →
    (Function.Surjective (groupMap f (n+1) x) ↔
      Function.Surjective (groupMap f (n+1) y))

private theorem surjectiveBasepoint_succ {n : ℕ} (h : SurjectiveBasepointInvariant.{u} n) :
    SurjectiveBasepointInvariant.{u} (n+1) := by
  intro X Y _ _ f x y p
  have hx : Function.Surjective
      (groupMap (PathSpace.conjugate p) (n+1) (Path.refl x)) :=
    (pathConjugation_isWeakHomotopyEquivalence p).2 n _ |>.2
  have hy : Function.Bijective
      (groupMap (PathSpace.conjugate (p.map f.continuous)) (n+1) (Path.refl (f x))) :=
    (pathConjugation_isWeakHomotopyEquivalence (p.map f.continuous)).2 n _
  calc
    _ ↔ Function.Surjective (groupMap (PathSpace.map f) (n+1) (Path.refl x)) :=
      loopDimensionShift_surjective_iff f (n+1) x
    _ ↔ Function.Surjective (groupMap
        ((PathSpace.conjugate (p.map f.continuous)).comp (PathSpace.map f))
          (n+1) (Path.refl x)) := by
      rw [groupMap_comp]
      exact (Function.Surjective.of_comp_iff' hy _).symm
    _ ↔ Function.Surjective (groupMap
        ((PathSpace.map f).comp (PathSpace.conjugate p)) (n+1) (Path.refl x)) := by
      rw [PathSpace.conjugate_naturality]
    _ ↔ Function.Surjective (groupMap (PathSpace.map f) (n+1)
        (PathSpace.conjugate p (Path.refl x))) := by
      rw [groupMap_comp]
      exact Function.Surjective.of_comp_iff _ hx
    _ ↔ Function.Surjective (groupMap (PathSpace.map f) (n+1) (Path.refl y)) :=
      h (PathSpace.map f) (PathSpace.conjugateConstantPath p)
    _ ↔ _ := (loopDimensionShift_surjective_iff f (n+1) y).symm

/-- Surjectivity in every positive degree depends only on the source path component. -/
theorem groupMap_surjective_path (n : ℕ) (f : C(X, Y)) {x y : X} (p : Path x y) :
    Function.Surjective (groupMap f (n+1) x) ↔
      Function.Surjective (groupMap f (n+1) y) := by
  have h : SurjectiveBasepointInvariant.{u} n := by
    induction n with
    | zero =>
      intro X Y _ _ f x y p
      exact groupMap_one_surjective_path f p
    | succ n h => exact surjectiveBasepoint_succ h
  exact h f p

end Thomason.Construction.HomotopyMaps

end

section

/-! # Restricting homotopies over a base to literal continuous fibres -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- The literal continuous fibre, with its subspace topology. -/
def continuousFiber {X B : TopCat.{0}} (p : X ⟶ B) (b : B) : TopCat.{0} :=
  TopCat.of {x : X // p.hom x = b}

def continuousFiberInclusion {X B : TopCat.{0}} (p : X ⟶ B) (b : B) :
    continuousFiber p b ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Any exact map over the base restricts to each literal fibre. -/
def continuousFiberMap {X Y B : TopCat.{0}} (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (f : X ⟶ Y) (hf : f ≫ q = p) : continuousFiber p b ⟶ continuousFiber q b :=
  TopCat.ofHom {
    toFun x := ⟨f.hom x.val, (congrArg (fun k => k.hom x.val) hf).trans x.property⟩
    continuous_toFun := (f.hom.continuous.comp continuous_subtype_val).subtype_mk _ }

@[reassoc] theorem continuousFiberMap_inclusion {X Y B : TopCat.{0}}
    (p : X ⟶ B) (q : Y ⟶ B) (b : B) (f : X ⟶ Y) (hf : f ≫ q = p) :
    continuousFiberMap p q b f hf ≫ continuousFiberInclusion q b =
      continuousFiberInclusion p b ≫ f := rfl

/-- An isomorphism over the base restricts to an isomorphism of fibres. -/
def continuousFiberIso {X Y B : TopCat.{0}} (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (e : X ≅ Y) (he : e.hom ≫ q = p) :
    continuousFiber p b ≅ continuousFiber q b where
  hom := continuousFiberMap p q b e.hom he
  inv := continuousFiberMap q p b e.inv (by rw [← he, e.inv_hom_id_assoc])
  hom_inv_id := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k => k.hom x.val) e.hom_inv_id
  inv_hom_id := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k => k.hom x.val) e.inv_hom_id

/-- A change of coordinates over the base preserves the weak-equivalence
property of the literal fibre inclusion. -/
theorem continuousFiberInclusion_weak_of_iso {X Y B : TopCat.{0}}
    (p : X ⟶ B) (q : Y ⟶ B) (b : B) (e : X ≅ Y) (he : e.hom ≫ q = p)
    (hq : topologicalWeakEquivalences (continuousFiberInclusion q b)) :
    topologicalWeakEquivalences (continuousFiberInclusion p b) := by
  apply topologicalWeakEquivalences.of_postcomp _ e.hom
    (topologicalWeakEquivalences.of_isIso _)
  rw [← continuousFiberMap_inclusion p q b e.hom he]
  exact topologicalWeakEquivalences.comp_mem _ _
    (topologicalWeakEquivalences.of_isIso (continuousFiberIso p q b e he).hom) hq

/-- The full parameterized homotopy restricts to the fibre when its base
coordinate is constant throughout. -/
def continuousFiberHomotopy {X Y B : TopCat.{0}} (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (f g : X ⟶ Y) (hf : f ≫ q = p) (hg : g ≫ q = p)
    (H : f.hom.Homotopy g.hom) (hH : ∀ t x, q.hom (H (t,x)) = p.hom x) :
    (continuousFiberMap p q b f hf).hom.Homotopy
      (continuousFiberMap p q b g hg).hom where
  toFun z := ⟨H (z.1, z.2.val), (hH _ _).trans z.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact H.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  map_zero_left x := Subtype.ext (H.map_zero_left x.val)
  map_one_left x := Subtype.ext (H.map_one_left x.val)

/-- A homotopy equivalence with both homotopies over the base induces an
actual homotopy equivalence on every continuous fibre. -/
def continuousFiberHomotopyEquiv {X Y B : TopCat.{0}} (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (f : X ⟶ Y) (g : Y ⟶ X) (hf : f ≫ q = p) (hg : g ≫ p = q)
    (H : (ContinuousMap.id X).Homotopy (g.hom.comp f.hom))
    (K : (ContinuousMap.id Y).Homotopy (f.hom.comp g.hom))
    (hH : ∀ t x, p.hom (H (t,x)) = p.hom x)
    (hK : ∀ t y, q.hom (K (t,y)) = q.hom y) :
    ContinuousMap.HomotopyEquiv (continuousFiber p b) (continuousFiber q b) where
  toFun := (continuousFiberMap p q b f hf).hom
  invFun := (continuousFiberMap q p b g hg).hom
  left_inv := ⟨(continuousFiberHomotopy p p b (𝟙 X) (f ≫ g) (Category.id_comp p)
    (by rw [Category.assoc, hg, hf]) H hH).symm.cast rfl rfl⟩
  right_inv := ⟨(continuousFiberHomotopy q q b (𝟙 Y) (g ≫ f) (Category.id_comp q)
    (by rw [Category.assoc, hf, hg]) K hK).symm.cast rfl rfl⟩

/-- The induced fibre map is a weak equivalence in all homotopy degrees. -/
theorem continuousFiberMap_weak_of_over_equivalence {X Y B : TopCat.{0}}
    (p : X ⟶ B) (q : Y ⟶ B) (b : B) (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : f ≫ q = p) (hg : g ≫ p = q)
    (H : (ContinuousMap.id X).Homotopy (g.hom.comp f.hom))
    (K : (ContinuousMap.id Y).Homotopy (f.hom.comp g.hom))
    (hH : ∀ t x, p.hom (H (t,x)) = p.hom x)
    (hK : ∀ t y, q.hom (K (t,y)) = q.hom y) :
    topologicalWeakEquivalences (continuousFiberMap p q b f hf) :=
  homotopyEquiv_isWeakHomotopyEquivalence
    (continuousFiberHomotopyEquiv p q b f g hf hg H K hH hK)

end

end Thomason.Construction

end

section

/-! # Exact maps of continuous fibres in a commutative square -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- A genuinely commutative square induces the literal map on its point
fibres, retaining the total-space point and the specified base point. -/
def continuousFiberBaseChangeMap {X Y A B : TopCat.{0}} (p : X ⟶ A) (q : Y ⟶ B)
    (f : X ⟶ Y) (g : A ⟶ B) (h : f ≫ q = p ≫ g) (b : A) :
    continuousFiber p b ⟶ continuousFiber q (g.hom b) :=
  TopCat.ofHom {
    toFun x := ⟨f.hom x.val, (congrArg (fun k => k.hom x.val) h).trans
      (congrArg g.hom x.property)⟩
    continuous_toFun := (f.hom.continuous.comp continuous_subtype_val).subtype_mk _ }

@[reassoc] theorem continuousFiberBaseChangeMap_inclusion {X Y A B : TopCat.{0}}
    (p : X ⟶ A) (q : Y ⟶ B) (f : X ⟶ Y) (g : A ⟶ B)
    (h : f ≫ q = p ≫ g) (b : A) :
    continuousFiberBaseChangeMap p q f g h b ≫ continuousFiberInclusion q (g.hom b) =
      continuousFiberInclusion p b ≫ f := rfl

/-- When both fibre inclusions and the total-space map are weak, the
specified map of literal fibres is weak as well. -/
theorem continuousFiberBaseChangeMap_weak {X Y A B : TopCat.{0}}
    (p : X ⟶ A) (q : Y ⟶ B) (f : X ⟶ Y) (g : A ⟶ B)
    (h : f ≫ q = p ≫ g) (b : A)
    (hf : topologicalWeakEquivalences f)
    (hp : topologicalWeakEquivalences (continuousFiberInclusion p b))
    (hq : topologicalWeakEquivalences (continuousFiberInclusion q (g.hom b))) :
    topologicalWeakEquivalences (continuousFiberBaseChangeMap p q f g h b) := by
  apply topologicalWeakEquivalences.of_postcomp _ _ hq
  rw [continuousFiberBaseChangeMap_inclusion]
  exact topologicalWeakEquivalences.comp_mem _ _ hp hf

end

end Thomason.Construction

end

section

/-! # Products with locally compact parameter spaces preserve colimits -/

namespace Thomason.Construction.TopologicalProduct

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

/-- Compact-open maps out of the fixed parameter space. -/
def mappingSpace (B : TopCat.{u}) : TopCat.{u} ⥤ TopCat.{u} where
  obj X := TopCat.of C(B, X)
  map f := TopCat.ofHom ⟨fun p => f.hom.comp p, ContinuousMap.continuous_postcomp f.hom⟩

/-- The ordinary compact-open exponential law, specialized to the parameter
spaces used in finite realization approximations. -/
def homEquiv (B : TopCat.{u}) [LocallyCompactSpace B] (X Y : TopCat.{u}) :
    ((tensorRight B).obj X ⟶ Y) ≃ (X ⟶ (mappingSpace B).obj Y) where
  toFun f := TopCat.ofHom f.hom.curry
  invFun f := TopCat.ofHom f.hom.uncurry
  left_inv f := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    rfl
  right_inv f := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply ContinuousMap.ext
    intro t
    rfl

/-- Product with a locally compact parameter is left adjoint to its
compact-open mapping-space functor. -/
def adjunction (B : TopCat.{u}) [LocallyCompactSpace B] :
    tensorRight B ⊣ mappingSpace B :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv B
    homEquiv_naturality_left_symm := by
      intro X' X Y f g
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      rfl
    homEquiv_naturality_right := by
      intro X Y Y' f g
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      apply ContinuousMap.ext
      intro t
      rfl }

theorem preservesColimits (B : TopCat.{u}) [LocallyCompactSpace B] :
    PreservesColimitsOfSize.{0,0} (tensorRight B) :=
  (adjunction B).leftAdjoint_preservesColimits

end Thomason.Construction.TopologicalProduct

end

section

/-! # Globular faces on the intelligent-truncation quotient -/

namespace Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

variable {C : StrictOmegaCategory.{0}} {n : ℕ}

theorem Rel.map_face {x y : C.bounded n} (h : Rel C n x y) (a : Bool) (m : ℕ) :
    Rel C n ((C.bounded n).face a m x) ((C.bounded n).face a m y) := by
  by_cases hmn : m < n
  · have he : (C.bounded n).face a m x = (C.bounded n).face a m y :=
      Subtype.ext (h.lower_faces a m hmn)
    rw [he]
    exact .refl _
  · have hx := (C.bounded n).dimensionLE_mono (show n ≤ m by omega)
      (C.bounded_isTruncated n x)
    have hy := (C.bounded n).dimensionLE_mono (show n ≤ m by omega)
      (C.bounded_isTruncated n y)
    have hx' : (C.bounded n).face a m x = x := by cases a; exact hx.1; exact hx.2
    have hy' : (C.bounded n).face a m y = y := by cases a; exact hy.1; exact hy.2
    rw [hx', hy']
    exact h

abbrev mk (x : C.bounded n) : Cell C n := Quotient.mk _ x

def face (a : Bool) (m : ℕ) (x : Cell C n) : Cell C n :=
  Quotient.liftOn x (fun z => mk ((C.bounded n).face a m z))
    (fun _ _ h => Quotient.sound (h.map_face a m))

@[simp] theorem face_mk (a : Bool) (m : ℕ) (x : C.bounded n) :
    face a m (mk x) = mk ((C.bounded n).face a m x) := rfl

/-- Below the truncation level, quotient equality of boundaries is actual equality. -/
theorem matching_of_quotient {m : ℕ} (hm : m < n) (x y : C.bounded n)
    (h : face true m (mk x) = face false m (mk y)) :
    (C.bounded n).target m x = (C.bounded n).source m y := by
  apply Rel.eq_of_dimensionLE (Quotient.exact h) hm
  · exact C.face_dimensionLE true m x.val
  · exact C.face_dimensionLE false m y.val

@[simp] theorem face_of_le {m : ℕ} (hm : n ≤ m) (a : Bool) (x : Cell C n) :
    face a m x = x := by
  induction x using Quotient.inductionOn with
  | h x =>
    have hx := (C.bounded n).dimensionLE_mono hm (C.bounded_isTruncated n x)
    cases a
    · exact congrArg mk hx.1
    · exact congrArg mk hx.2

theorem globular (a b : Bool) (k m : ℕ) (x : Cell C n) :
    face a k (face b m x) = if k < m then face a k x else face b m x := by
  induction x using Quotient.inductionOn with
  | h x =>
    change mk ((C.bounded n).face a k ((C.bounded n).face b m x)) =
      if k < m then mk ((C.bounded n).face a k x) else mk ((C.bounded n).face b m x)
    rw [(C.bounded n).globular]
    split_ifs <;> rfl

end Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

end

section

/-! # Composition on the intelligent-truncation quotient -/

namespace Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

variable {C : StrictOmegaCategory.{0}} {n : ℕ}

noncomputable def representative (x : Cell C n) : C.bounded n := Quotient.out x

@[simp] theorem mk_representative (x : Cell C n) : mk (representative x) = x :=
  Quotient.out_eq x

/-- Below the surviving dimension the quotient does not invent matching boundaries. -/
theorem representatives_match {m : ℕ} (hm : m < n) (x y : Cell C n)
    (h : face true m x = face false m y) :
    (C.bounded n).target m (representative x) = (C.bounded n).source m (representative y) := by
  apply matching_of_quotient hm
  simpa only [mk_representative] using h

noncomputable def comp (m : ℕ) (x y : Cell C n)
    (h : face true m x = face false m y) : Cell C n :=
  if hm : m < n then mk ((C.bounded n).comp m (representative x) (representative y)
    (representatives_match hm x y h)) else x

/-- Every choice of matching representatives computes the same quotient composite. -/
theorem comp_mk (m : ℕ) (x y : C.bounded n)
    (h : (C.bounded n).target m x = (C.bounded n).source m y)
    (h' : face true m (mk x) = face false m (mk y)) :
    comp m (mk x) (mk y) h' = mk ((C.bounded n).comp m x y h) := by
  by_cases hm : m < n
  · simp only [comp, dite_eq_left hm]
    apply Quotient.sound
    apply Rel.compose
    · exact Quotient.exact (mk_representative (mk x))
    · exact Quotient.exact (mk_representative (mk y))
  · simp only [comp, dite_eq_right hm]
    have hx := (C.bounded n).dimensionLE_mono (show n ≤ m by omega)
      (C.bounded_isTruncated n x)
    have hy := (C.bounded n).dimensionLE_mono (show n ≤ m by omega)
      (C.bounded_isTruncated n y)
    have hxy : x = y := hx.2.symm.trans (h.trans hy.1)
    have hc : (C.bounded n).comp m x y h = y :=
      (C.bounded n).comp_of_dimensionLE (show n ≤ m by omega) (C.bounded_isTruncated n x) h
    exact congrArg mk (hxy.trans hc.symm)

/-- Source compatibility, including identity levels above the cutoff. -/
theorem source_comp (m : ℕ) (x y : Cell C n)
    (h : face true m x = face false m y) :
    face false m (comp m x y h) = face false m x := by
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      by_cases hm : m < n
      · have hc := matching_of_quotient hm x y h
        rw [comp_mk m x y hc h]
        exact congrArg mk ((C.bounded n).source_comp m x y hc)
      · simp only [comp, dite_eq_right hm]

/-- Target compatibility uses the original matching condition. -/
theorem target_comp (m : ℕ) (x y : Cell C n)
    (h : face true m x = face false m y) :
    face true m (comp m x y h) = face true m y := by
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      by_cases hm : m < n
      · have hc := matching_of_quotient hm x y h
        rw [comp_mk m x y hc h]
        exact congrArg mk ((C.bounded n).target_comp m x y hc)
      · simp only [comp, dite_eq_right hm]
        have hn : n ≤ m := by omega
        rw [face_of_le hn true, face_of_le hn false] at h
        simpa only [face_of_le hn] using h

end Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

end

end OAI
