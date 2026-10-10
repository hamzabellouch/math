import OAI.CategoryTheory.Thomason.Chains.SimplexBasisHeight
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeUniversal
import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Strict.StrictCompositeListReplacement
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Find

namespace OAI

section

/-! # Choosing the decomposition level of a generated expression

The second-highest generator occurrence determines the normalization
level in Steiner 2004, Proposition 4.2. Multiplicity is retained: two
occurrences of the same generator count as two occurrences.
-/

namespace Thomason.Construction.StrictOmegaCategory.ExpressionDegree

variable {I : Type}

/-- Number of generator occurrences strictly above the chosen level. -/
def highCount (d : I → ℕ) (r : ℕ) (xs : List I) : ℕ :=
  (xs.filter (fun i => decide (r < d i))).length

/-- A finite upper bound for every generator occurrence. -/
def maximum (d : I → ℕ) : List I → ℕ
  | [] => 0
  | i :: xs => max (d i) (maximum d xs)

theorem le_maximum (d : I → ℕ) {xs : List I} {i : I} (hi : i ∈ xs) :
    d i ≤ maximum d xs := by
  induction xs with
  | nil => simp at hi
  | cons j xs ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact le_max_left _ _
    · exact (ih hi).trans (le_max_right _ _)

theorem highCount_append (d : I → ℕ) (r : ℕ) (xs ys : List I) :
    highCount d r (xs ++ ys) = highCount d r xs + highCount d r ys := by
  simp [highCount]

theorem highCount_zero (d : I → ℕ) (xs : List I) {r : ℕ}
    (hr : maximum d xs ≤ r) : highCount d r xs = 0 := by
  have hf : xs.filter (fun i => decide (r < d i)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi
    simpa only [decide_eq_true_eq] using not_lt_of_ge ((le_maximum d hi).trans hr)
  simp only [highCount, hf, List.length_nil]

/-- The critical level has at least two higher occurrences, and at most
one occurrence strictly above its successor. -/
theorem exists_critical_level (d : I → ℕ) (xs : List I) (n : ℕ)
    (hn : 2 ≤ highCount d n xs) :
    ∃ r, n ≤ r ∧ 2 ≤ highCount d r xs ∧ highCount d (r+1) xs ≤ 1 := by
  let M := maximum d xs
  have hnM : n ≤ M := by
    by_contra h
    have hz := highCount_zero d xs (show maximum d xs ≤ n by dsimp [M] at h; omega)
    omega
  let P := fun r => 2 ≤ highCount d r xs
  let r := Nat.findGreatest P M
  have hr : P r := Nat.findGreatest_spec hnM hn
  have hnr : n ≤ r := Nat.le_findGreatest hnM hn
  have hnext : ¬ P (r+1) := by
    by_cases hle : r+1 ≤ M
    · exact (Nat.findGreatest_eq_iff.mp (show Nat.findGreatest P M = r from rfl)).2.2
        (Nat.lt_succ_self r) hle
    · have hz := highCount_zero d xs (show maximum d xs ≤ r+1 by dsimp [M] at hle; omega)
      dsimp [P]
      rw [hz]
      omega
  exact ⟨r, hnr, hr, by dsimp [P] at hnext; omega⟩

end Thomason.Construction.StrictOmegaCategory.ExpressionDegree

end

section

/-! # Removing identity factors from generated expressions

Every composition-generated cell has an expression in which each binary
composition has two nonidentity factors at its composition level. For such
an expression the second-highest generator degree bounds every composition
level. This is the reduction preceding Steiner's Proposition 4.2.
-/

namespace Thomason.Construction.StrictOmegaCategory

variable {C : StrictOmegaCategory.{0}} {I : Type} {g : I → C}

theorem comp_eq_left_of_dimensionLE {x y : C} (r : ℕ)
    (hxy : C.target r x = C.source r y) (hy : C.DimensionLE r y) :
    C.comp r x y hxy = x := by
  have he : y = C.target r x := hy.1.symm.trans hxy.symm
  subst y
  exact C.right_unit r x hxy

/-- A generated expression with every identity factor removed. -/
inductive EssentialExpression (C : StrictOmegaCategory.{0}) {I : Type} (g : I → C) :
    C → Type
  | generator (i : I) : EssentialExpression C g (g i)
  | comp {x y : C} (r : ℕ) (hxy : C.target r x = C.source r y)
      (tx : EssentialExpression C g x) (ty : EssentialExpression C g y)
      (hx : ¬ C.DimensionLE r x) (hy : ¬ C.DimensionLE r y) :
      EssentialExpression C g (C.comp r x y hxy)

namespace EssentialExpression

def expression {x : C} : EssentialExpression C g x → CompositionExpression C g x
  | .generator i => .generator i
  | .comp r hxy tx ty _ _ => .comp r hxy tx.expression ty.expression

/-- Every internal composition level is at most the given bound. -/
def levelsLE (r : ℕ) {x : C} : EssentialExpression C g x → Prop
  | .generator _ => True
  | .comp n _ tx ty _ _ => n ≤ r ∧ tx.levelsLE r ∧ ty.levelsLE r

end EssentialExpression

namespace CompositionExpression

/-- Unit laws remove all inessential composition nodes. -/
theorem exists_essential {x : C} (t : CompositionExpression C g x) :
    Nonempty (EssentialExpression C g x) := by
  classical
  induction t with
  | generator i => exact ⟨.generator i⟩
  | @comp x y r hxy tx ty ihx ihy =>
    by_cases hx : C.DimensionLE r x
    · rw [C.comp_of_dimensionLE (Nat.le_refl r) hx hxy]
      exact ihy
    · by_cases hy : C.DimensionLE r y
      · rw [comp_eq_left_of_dimensionLE r hxy hy]
        exact ihx
      · obtain ⟨sx⟩ := ihx
        obtain ⟨sy⟩ := ihy
        exact ⟨.comp r hxy sx sy hx hy⟩

end CompositionExpression

namespace ExpressionDegree

theorem highCount_eq_zero_iff (d : I → ℕ) (r : ℕ) (xs : List I) :
    highCount d r xs = 0 ↔ ∀ i ∈ xs, d i ≤ r := by
  simp only [highCount, List.length_eq_zero_iff, List.filter_eq_nil_iff,
    Bool.not_eq_true, decide_eq_false_iff_not, not_lt]

theorem highCount_pos_of_not_dimensionLE (d : I → ℕ)
    (hg : ∀ i, C.DimensionLE (d i) (g i)) {x : C}
    (t : CompositionExpression C g x) (r : ℕ) (hx : ¬ C.DimensionLE r x) :
    0 < highCount d r t.labels := by
  by_contra h
  have hz : highCount d r t.labels = 0 := by omega
  exact hx (t.dimensionLE d hg r ((highCount_eq_zero_iff d r t.labels).mp hz))

end ExpressionDegree

namespace EssentialExpression

open ExpressionDegree

/-- With at most one generator above r+1, essential compositions occur
only at levels at most r. -/
theorem levelsLE_of_highCount (d : I → ℕ)
    (hg : ∀ i, C.DimensionLE (d i) (g i)) {x : C}
    (t : EssentialExpression C g x) (r : ℕ)
    (hcount : highCount d (r+1) t.expression.labels ≤ 1) : t.levelsLE r := by
  induction t with
  | generator i => trivial
  | @comp x y n hxy tx ty hx hy ihx ihy =>
    have hsum : highCount d (r+1) tx.expression.labels +
        highCount d (r+1) ty.expression.labels ≤ 1 := by
      simpa only [expression, CompositionExpression.labels, highCount_append] using hcount
    refine ⟨?_, ihx (by omega), ihy (by omega)⟩
    by_contra hn
    have hn' : r+1 ≤ n := by omega
    have hxx : ¬ C.DimensionLE (r+1) x :=
      fun h => hx (C.dimensionLE_mono hn' h)
    have hyy : ¬ C.DimensionLE (r+1) y :=
      fun h => hy (C.dimensionLE_mono hn' h)
    have hp := highCount_pos_of_not_dimensionLE d hg tx.expression (r+1) hxx
    have hq := highCount_pos_of_not_dimensionLE d hg ty.expression (r+1) hyy
    omega

/-- A nongenerator essential expression has a critical level with at
least two higher occurrences, at most one above the next level, and no
composition above the critical level. -/
theorem generator_or_critical (d : I → ℕ)
    (hg : ∀ i, C.DimensionLE (d i) (g i)) {x : C}
    (t : EssentialExpression C g x) :
    (∃ i, x = g i) ∨ ∃ r,
      2 ≤ highCount d r t.expression.labels ∧
      highCount d (r+1) t.expression.labels ≤ 1 ∧ t.levelsLE r := by
  cases t with
  | generator i => exact Or.inl ⟨i, rfl⟩
  | @comp x y n hxy tx ty hx hy =>
    have hp := highCount_pos_of_not_dimensionLE d hg tx.expression n hx
    have hq := highCount_pos_of_not_dimensionLE d hg ty.expression n hy
    have htwo : 2 ≤ highCount d n
        (CompositionExpression.comp n hxy tx.expression ty.expression).labels := by
      simp only [CompositionExpression.labels, highCount_append]
      omega
    obtain ⟨r, _, hr, hr'⟩ := exists_critical_level d
      (CompositionExpression.comp n hxy tx.expression ty.expression).labels n htwo
    exact Or.inr ⟨r, hr, hr',
      (EssentialExpression.comp n hxy tx ty hx hy).levelsLE_of_highCount d hg r hr'⟩

end EssentialExpression
end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Strings with one higher generator in each factor

These retain actual composition expressions for the factors, rather than
only a statement about their images in a directed complex.
-/

namespace Thomason.Construction.StrictOmegaCategory

open ExpressionDegree

variable {C : StrictOmegaCategory.{0}} {I : Type} {g : I → C} {d : I → ℕ}

/-- An r-string with exactly one generator of degree greater than r in
each factor. Its length is retained for the normalization induction. -/
inductive HighGeneratorString (C : StrictOmegaCategory.{0}) {I : Type}
    (g : I → C) (d : I → ℕ) (r : ℕ) : C → ℕ → Prop
  | singleton {x : C} (t : CompositionExpression C g x)
      (ht : highCount d r t.labels = 1) : HighGeneratorString C g d r x 1
  | cons {x y : C} {n : ℕ} (t : CompositionExpression C g x)
      (ht : highCount d r t.labels = 1)
      (tail : HighGeneratorString C g d r y n)
      (hxy : C.target r x = C.source r y) :
      HighGeneratorString C g d r (C.comp r x y hxy) (n+1)

namespace HighGeneratorString

variable {r : ℕ}

theorem length_pos {x : C} {n : ℕ} (h : HighGeneratorString C g d r x n) : 0 < n := by
  cases h <;> omega

/-- Forgetting the expressions gives a literal strict composite list. -/
theorem exists_list {x : C} {n : ℕ} (h : HighGeneratorString C g d r x n) :
    ∃ xs : List C, xs.length = n ∧ CompositeList C r xs x ∧
      ∀ y ∈ xs, ∃ t : CompositionExpression C g y, highCount d r t.labels = 1 := by
  induction h with
  | @singleton x t ht =>
    exact ⟨[x], rfl, .singleton x, by simpa only [List.mem_singleton] using
      (fun y (hy : y = x) => by subst y; exact ⟨t, ht⟩)⟩
  | @cons x y n t ht tail hxy ih =>
    obtain ⟨xs, hlen, hxs, hprop⟩ := ih
    refine ⟨x :: xs, by simp only [List.length_cons, hlen], .cons x hxs hxy, ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨t, ht⟩
    · exact hprop z hz

/-- Concatenation retains the one-generator condition on each factor. -/
theorem append {x y : C} {n m : ℕ}
    (hx : HighGeneratorString C g d r x n)
    (hy : HighGeneratorString C g d r y m)
    (hxy : C.target r x = C.source r y) :
    HighGeneratorString C g d r (C.comp r x y hxy) (n+m) := by
  induction hx with
  | @singleton x t ht =>
    simpa only [Nat.add_comm 1 m] using HighGeneratorString.cons t ht hy hxy
  | @cons z x n t ht tail hzx ih =>
    have hxy' : C.target r x = C.source r y :=
      (C.target_comp r z x hzx).symm.trans hxy
    have hzxy : C.target r z = C.source r (C.comp r x y hxy') :=
      hzx.trans (C.source_comp r x y hxy').symm
    have hh := HighGeneratorString.cons t ht (ih hxy') hzxy
    simpa only [Nat.add_assoc, Nat.add_comm 1 m,
      C.assoc r z x y hzx hxy' hxy hzxy] using hh

/-- Right whiskering by an r-dimensional expression distributes over
an r-string and introduces no higher generator. -/
theorem whisker_right {x y : C} {n m : ℕ}
    (hx : HighGeneratorString C g d r x n)
    (ty : CompositionExpression C g y)
    (hty : highCount d r ty.labels = 0) (hy : C.DimensionLE r y)
    (hmr : m < r) (hxy : C.target m x = C.source m y) :
    HighGeneratorString C g d r (C.comp m x y hxy) n := by
  induction hx with
  | @singleton x tx htx =>
    exact .singleton (.comp m hxy tx ty) (by
      simp only [CompositionExpression.labels, highCount_append, htx, hty, Nat.add_zero])
  | @cons z x n tz htz tail hzx ih =>
    have hz : C.target m z = C.source m y :=
      (C.lower_face_comp true hmr z x hzx).symm.trans hxy
    have hx : C.target m x = C.source m y :=
      (C.lower_faces_equal true hmr z x hzx).symm.trans hz
    have hyy : C.target r y = C.source r y := hy.2.trans hy.1.symm
    have hzt : C.target m (C.target r z) = C.source m (C.target r y) := by
      simpa only [target, source, C.globular, hmr, ite_true] using hz
    have hxs : C.target m (C.source r x) = C.source m (C.source r y) := by
      simpa only [target, source, C.globular, hmr, ite_true] using hx
    have hcross : C.target r (C.comp m z y hz) = C.source r (C.comp m x y hx) := by
      change C.face true r (C.comp m z y hz) = C.face false r (C.comp m x y hx)
      rw [C.face_comp true r m hmr z y hz hzt,
        C.face_comp false r m hmr x y hx hxs]
      simp only [hzx, hy.1, hy.2]
    have houter : C.target m (C.comp r z x hzx) =
        C.source m (C.comp r y y hyy) :=
      (C.lower_face_comp true hmr z x hzx).trans
        (hz.trans (C.lower_face_comp false hmr y y hyy).symm)
    have he := C.interchange m r hmr z y x y hz hx hzx hyy hcross houter
    have hey : C.comp r y y hyy = y := C.comp_of_dimensionLE (Nat.le_refl r) hy hyy
    have he' : C.comp r (C.comp m z y hz) (C.comp m x y hx) hcross =
        C.comp m (C.comp r z x hzx) y hxy := by
      simpa only [hey] using he
    rw [← he']
    exact .cons (.comp m hz tz ty) (by
      simp only [CompositionExpression.labels, highCount_append, htz, hty, Nat.add_zero])
      (ih hx) hcross

/-- Left whiskering by an r-dimensional expression likewise preserves
the number and higher-generator content of the factors. -/
theorem whisker_left {x y : C} {n m : ℕ}
    (ty : HighGeneratorString C g d r y n)
    (tx : CompositionExpression C g x)
    (htx : highCount d r tx.labels = 0) (hx : C.DimensionLE r x)
    (hmr : m < r) (hxy : C.target m x = C.source m y) :
    HighGeneratorString C g d r (C.comp m x y hxy) n := by
  induction ty with
  | @singleton y ty hty =>
    exact .singleton (.comp m hxy tx ty) (by
      simp only [CompositionExpression.labels, highCount_append, htx, hty, Nat.zero_add])
  | @cons z y n tz htz tail hzy ih =>
    have hz : C.target m x = C.source m z :=
      hxy.trans (C.lower_face_comp false hmr z y hzy)
    have hy : C.target m x = C.source m y :=
      hz.trans (C.lower_faces_equal false hmr z y hzy)
    have hxx : C.target r x = C.source r x := hx.2.trans hx.1.symm
    have hzt : C.target m (C.target r x) = C.source m (C.target r z) := by
      simpa only [target, source, C.globular, hmr, ite_true] using hz
    have hys : C.target m (C.source r x) = C.source m (C.source r y) := by
      simpa only [target, source, C.globular, hmr, ite_true] using hy
    have hcross : C.target r (C.comp m x z hz) = C.source r (C.comp m x y hy) := by
      change C.face true r (C.comp m x z hz) = C.face false r (C.comp m x y hy)
      rw [C.face_comp true r m hmr x z hz hzt,
        C.face_comp false r m hmr x y hy hys]
      simp only [hzy, hx.1, hx.2]
    have houter : C.target m (C.comp r x x hxx) =
        C.source m (C.comp r z y hzy) :=
      (C.lower_face_comp true hmr x x hxx).trans
        (hz.trans (C.lower_face_comp false hmr z y hzy).symm)
    have he := C.interchange m r hmr x z x y hz hy hxx hzy hcross houter
    have hex : C.comp r x x hxx = x := C.comp_of_dimensionLE (Nat.le_refl r) hx hxx
    have he' : C.comp r (C.comp m x z hz) (C.comp m x y hy) hcross =
        C.comp m x (C.comp r z y hzy) hxy := by
      simpa only [hex] using he
    rw [← he']
    exact .cons (.comp m hz tx tz) (by
      simp only [CompositionExpression.labels, highCount_append, htx, htz, Nat.zero_add])
      (ih hy) hcross

end HighGeneratorString
end Thomason.Construction.StrictOmegaCategory

end

section

/-! # The cell obtained by tensoring a cell with the interval edge

The alternating endpoint convention agrees with the right chain tensor.
This explicit positive globular table is used to construct higher simplex
cells; it does not assume a Gray tensor or a simplex-atom theorem.
-/

namespace Thomason.Construction.DirectedComplex.RightCylinder

variable {K : DirectedComplex}

/-- The full table of the tensor of a globular cell with the oriented edge. -/
def intervalCellTable (x : Cell K) (a : Bool) : (n : ℕ) → (rightCylinder K).group n
  | 0 => if a then (0, x.table a 0) else (x.table a 0, 0)
  | n + 1 =>
      if Even n then
        if a then (x.table a (n + 1), 0, x.table a n)
        else (0, x.table a (n + 1), x.table a n)
      else
        if a then (0, x.table a (n + 1), x.table a n)
        else (x.table a (n + 1), 0, x.table a n)

/-- The alternating endpoint table has the required tensor differential. -/
theorem intervalCellTable_boundary (x : Cell K) (a : Bool) (n : ℕ) :
    (rightCylinder K).differential n (intervalCellTable x a (n + 1)) =
      intervalCellTable x true n - intervalCellTable x false n := by
  cases n with
  | zero =>
    cases a <;> ext <;>
      simp [intervalCellTable, rightCylinder, differential, x.boundary]
  | succ n =>
    by_cases he : Even n
    · have hnext : ¬Even (n + 1) := by
        rw [Nat.even_add_one]
        exact not_not.mpr he
      have hsign : (-1 : ℤ) ^ (n + 1) = -1 := by
        rw [pow_succ, he.neg_one_pow]
        simp
      cases a <;> ext <;>
        simp [intervalCellTable, rightCylinder, differential, he, hnext, hsign, x.boundary]
      all_goals abel
    · have hnext : Even (n + 1) := by
        rw [Nat.even_add_one]
        exact he
      have hodd : Odd n := Nat.not_even_iff_odd.mp he
      have hsign : (-1 : ℤ) ^ (n + 1) = 1 := by
        rw [pow_succ, hodd.neg_one_pow]
        simp
      cases a <;> ext <;>
        simp [intervalCellTable, rightCylinder, differential, he, hnext, hsign, x.boundary]

/-- Tensoring a cell with the edge produces an actual positive globular cell. -/
def intervalCell (x : Cell K) : Cell (rightCylinder K) where
  table := intervalCellTable x
  positive a n := by
    cases n with
    | zero =>
      cases a
      · exact ⟨x.positive _ _, (K.positive _).zero_mem⟩
      · exact ⟨(K.positive _).zero_mem, x.positive _ _⟩
    | succ n =>
      by_cases he : Even n <;> cases a <;>
        simp only [intervalCellTable, he, ↓reduceIte]
      · exact ⟨(K.positive _).zero_mem, x.positive _ _, x.positive _ _⟩
      · exact ⟨x.positive _ _, (K.positive _).zero_mem, x.positive _ _⟩
      · exact ⟨x.positive _ _, (K.positive _).zero_mem, x.positive _ _⟩
      · exact ⟨(K.positive _).zero_mem, x.positive _ _, x.positive _ _⟩
  augmentation a := by
    cases a <;> simp [intervalCellTable, rightCylinder, augmentation, x.augmentation]
  boundary := intervalCellTable_boundary x
  finite_support := by
    obtain ⟨N, hN⟩ := x.finite_support
    refine ⟨N + 1, ?_⟩
    intro n hn a
    cases n with
    | zero => omega
    | succ n =>
      have hn' : N < n := by omega
      have hn'' : N < n + 1 := by omega
      simp only [intervalCellTable, hN n hn', hN (n + 1) hn'']
      split_ifs <;> rfl

/-- The source is the initial endpoint applied to the old source. -/
theorem intervalCell_source (x : Cell K) :
    (intervalCell x).face false 0 = Cell.map (endpoint K false) (x.face false 0) := by
  apply Cell.ext
  funext a n
  cases n with
  | zero =>
    cases a <;> rfl
  | succ n =>
    simp [Cell.map, Cell.face, Cell.cutTable, endpoint, endpointMap]
    rfl

/-- The target is the final endpoint applied to the old target. -/
theorem intervalCell_target (x : Cell K) :
    (intervalCell x).face true 0 = Cell.map (endpoint K true) (x.face true 0) := by
  apply Cell.ext
  funext a n
  cases n with
  | zero =>
    cases a <;> rfl
  | succ n =>
    simp [Cell.map, Cell.face, Cell.cutTable, endpoint, endpointMap]
    rfl

end Thomason.Construction.DirectedComplex.RightCylinder

end

section

/-! # Retracts of actual realization weak equivalences

The based homotopy-group functors carry the original retract diagram to
retracts of bijections. This does not use any model-category axiom.
-/

namespace Thomason.Construction

open CategoryTheory

universe u

namespace PointedHomotopyGroups

variable {X Y Z W : TopCat.{u}} {f : X ⟶ Y} {g : Z ⟶ W}

def pointedRetractArrow (h : RetractArrow f g) (x : X) :
    RetractArrow (pointedMap f (x := x) rfl)
      (pointedMap g (congrArg (fun k => k.hom x) h.i_w)) where
  i := Arrow.homMk (pointedMap h.i.left rfl) (pointedMap h.i.right rfl) (by
    apply Under.UnderMorphism.ext
    exact h.i_w)
  r := Arrow.homMk
    (pointedMap h.r.left (congrArg (fun k => k.hom x) h.retract_left))
    (pointedMap h.r.right (congrArg (fun k => k.hom (f.hom x)) h.retract_right)) (by
      apply Under.UnderMorphism.ext
      exact h.r_w)
  retract := by
    apply Arrow.hom_ext
    · apply Under.UnderMorphism.ext
      exact h.retract_left
    · apply Under.UnderMorphism.ext
      exact h.retract_right

end PointedHomotopyGroups

/-- Weak equivalences of spaces are closed under retracts, for their actual
component and based homotopy-group definition. -/
instance : topologicalWeakEquivalences.{u}.IsStableUnderRetracts where
  of_retract {X Y Z W f g} h hg := by
    constructor
    · let F := PointedHomotopyGroups.componentsFunctor.{u}
      have : IsIso (F.map g) := (isIso_iff_bijective _).mpr hg.1
      have hi : IsIso (F.map f) := MorphismProperty.of_retract (P :=
        MorphismProperty.isomorphisms (Type u)) (h.map F) (by infer_instance)
      exact (isIso_iff_bijective _).mp hi
    · intro n x
      let F := PointedHomotopyGroups.homotopyGroupFunctor.{u} (n+1)
      let hp := PointedHomotopyGroups.pointedRetractArrow h x
      have hg' : IsIso (F.map (PointedHomotopyGroups.pointedMap g
          (congrArg (fun k => k.hom x) h.i_w))) := by
        apply (isIso_iff_bijective _).mpr
        exact (PointedHomotopyGroups.map_bijective_iff _ _ _).mpr (hg.2 n (h.i.left.hom x))
      have hf' : IsIso (F.map (PointedHomotopyGroups.pointedMap f (x := x) rfl)) :=
        MorphismProperty.of_retract (P := MorphismProperty.isomorphisms (Type u))
          (hp.map F) (by infer_instance)
      exact (PointedHomotopyGroups.map_bijective_iff _ _ _).mp
        ((isIso_iff_bijective _).mp hf')

/-- The same unconditional retract law holds for geometric realizations. -/
instance : realizationWeakEquivalences.{u}.IsStableUnderRetracts :=
  inferInstanceAs (topologicalWeakEquivalences.{u}.inverseImage SSet.toTop).IsStableUnderRetracts

end Thomason.Construction

end

section

/-! # Direct cancellation for realization weak equivalences

Cancellation of a weak postcomposition is pointwise on homotopy groups.
Cancellation of a weak precomposition is also pointwise when the continuous
map is surjective. Neither proof invokes the Kan–Quillen theorem.
-/

namespace Thomason.Construction

open CategoryTheory

universe u

namespace IsWeakHomotopyEquivalence

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] {f : C(X, Y)} {g : C(Y, Z)}

theorem of_postcomp (hg : IsWeakHomotopyEquivalence g)
    (hfg : IsWeakHomotopyEquivalence (g.comp f)) : IsWeakHomotopyEquivalence f := by
  constructor
  · apply (hg.1.of_comp_iff' _).mp
    simpa only [HomotopyMaps.componentsMap_comp] using hfg.1
  · intro n x
    apply ((hg.2 n (f x)).of_comp_iff' _).mp
    simpa only [HomotopyMaps.groupMap_comp] using hfg.2 n x

theorem of_precomp_of_surjective (hf : IsWeakHomotopyEquivalence f)
    (hfg : IsWeakHomotopyEquivalence (g.comp f)) (hs : Function.Surjective f) :
    IsWeakHomotopyEquivalence g := by
  constructor
  · apply (hf.1.of_comp_iff _).mp
    simpa only [HomotopyMaps.componentsMap_comp] using hfg.1
  · intro n y
    obtain ⟨x, rfl⟩ := hs y
    apply ((hf.2 n x).of_comp_iff _).mp
    simpa only [HomotopyMaps.groupMap_comp] using hfg.2 n x

end IsWeakHomotopyEquivalence

instance : topologicalWeakEquivalences.{u}.HasOfPostcompProperty
    topologicalWeakEquivalences.{u} where
  of_postcomp _ _ hg hfg := IsWeakHomotopyEquivalence.of_postcomp hg hfg

instance : realizationWeakEquivalences.{u}.HasOfPostcompProperty
    realizationWeakEquivalences.{u} where
  of_postcomp f g hg hfg := by
    apply topologicalWeakEquivalences.of_postcomp (SSet.toTop.map f) (SSet.toTop.map g) hg
    change topologicalWeakEquivalences (SSet.toTop.map (f ≫ g)) at hfg
    simpa only [Functor.map_comp] using hfg

/-- A weak surjective continuous map can be cancelled on the source side. -/
theorem topologicalWeakEquivalences_of_precomp_of_surjective
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : topologicalWeakEquivalences f) (hfg : topologicalWeakEquivalences (f ≫ g))
    (hs : Function.Surjective f.hom) : topologicalWeakEquivalences g :=
  hf.of_precomp_of_surjective hfg hs

end Thomason.Construction

end

section

/-! # Based homotopies act identically on the actual homotopy groups

These proofs use explicit homotopies of generalized loops. They need no
Kan–Quillen weak factorization systems or weak-equivalence axioms.
-/

namespace Thomason.Construction.HomotopyMaps

open CategoryTheory

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)} {x : X} {y : Y}

/-- A homotopy fixed at the basepoint gives homotopic postcomposed loops. -/
def basedLoopHomotopy (H : f.HomotopyRel g {x}) (ef : f x = y) (eg : g x = y)
    {N : Type*} (p : GenLoop N X x) :
    (basedLoopMap f ef p).val.HomotopyRel (basedLoopMap g eg p).val (Cube.boundary N) where
  toHomotopy := H.toHomotopy.compContinuousMap p.val
  prop' t z hz := by
    change H (t, p z) = f (p z)
    exact (congrArg (fun w => H (t, w)) (p.property z hz)).trans
      ((H.eq_fst t (Set.mem_singleton x)).trans (congrArg f (p.property z hz)).symm)

/-- The induced maps agree, including the explicit target-basepoint transports. -/
theorem basedGroupMap_homotopy (H : f.HomotopyRel g {x})
    (ef : f x = y) (eg : g x = y) (n : ℕ) :
    basedGroupMap f ef n = basedGroupMap g eg n := by
  funext a
  induction a using Quotient.inductionOn with
  | h p => exact Quotient.sound ⟨basedLoopHomotopy H ef eg p⟩

/-- Unbased homotopies give the same function on path components. -/
theorem componentsMap_homotopy (H : f.Homotopy g) : componentsMap f = componentsMap g := by
  funext a
  induction a using ZerothHomotopy.rec with
  | mk a =>
    apply ZerothHomotopy.sound
    exact {
      toFun := fun t => H (t, a)
      continuous_toFun := H.continuous.comp (by fun_prop)
      source' := H.apply_zero a
      target' := H.apply_one a }

/-- A based homotopy preserves the bijectivity test at that basepoint. -/
theorem groupMap_bijective_homotopy_iff (H : f.HomotopyRel g {x}) (n : ℕ) :
    Function.Bijective (groupMap f n x) ↔ Function.Bijective (groupMap g n x) := by
  have e := H.fst_eq_snd (Set.mem_singleton x)
  rw [← basedGroupMap_bijective_iff g e.symm n]
  rw [← basedGroupMap_homotopy H rfl e.symm n]
  rfl

end Thomason.Construction.HomotopyMaps

end

section

/-! # The signed boundary order on actual normalized simplex bases

Negative boundary terms have smaller height and positive terms have larger
height. All degrees use one common integer-valued height, so this excludes
cycles involving different-dimensional boundary incidences.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

/-- The decreasing ternary exponents associated to a simplex basis. -/
def basisWeights {m p : ℕ} (b : Basis m p) : List ℕ :=
  List.ofFn (fun i => m - (b i).val)

theorem basisWeights_decreasing {m p : ℕ} (b : Basis m p) :
    (basisWeights b).Pairwise (· > ·) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  have hb := b.strictMono hij
  have hi := (b i).isLt
  have hj := (b j).isLt
  change m - (b j).val < m - (b i).val
  omega

/-- Removing an entry from a finite tuple agrees with skipping its index. -/
theorem ofFn_succAbove {α : Type*} {n : ℕ} (f : Fin (n+1) → α) (i : Fin (n+1)) :
    List.ofFn (fun j : Fin n => f (i.succAbove j)) = (List.ofFn f).eraseIdx i.val := by
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_eraseIdx_of_lt (by simpa using i.isLt),
      List.length_ofFn]
    omega
  · intro j hj hk
    simp only [List.getElem_ofFn, List.getElem_eraseIdx]
    by_cases hji : j < i.val
    · rw [dite_eq_left hji, Fin.succAbove_of_castSucc_lt _ _ hji]
      rfl
    · rw [dite_eq_right hji, Fin.succAbove_of_le_castSucc]
      · rfl
      · exact Nat.le_of_not_gt hji

theorem basisWeights_deleteVertex {m p : ℕ} (b : Basis m (p+1)) (i : Fin (p+2)) :
    basisWeights (deleteVertex b i) = (basisWeights b).eraseIdx i.val :=
  ofFn_succAbove (fun j => m - (b j).val) i

/-- A common height on the normalized bases of every degree. -/
def basisHeight {m p : ℕ} (b : Basis m p) : ℤ := alternatingHeight (basisWeights b)

/-- Every literal face has the sign dictated by its position in the boundary. -/
theorem basisHeight_deleteVertex {m p : ℕ} (b : Basis m (p+1)) (i : Fin (p+2)) :
    0 < (-1 : ℤ)^i.val * (basisHeight (deleteVertex b i) - basisHeight b) := by
  unfold basisHeight
  rw [basisWeights_deleteVertex]
  apply alternatingHeight_eraseIdx _ (basisWeights_decreasing b) i.val
  simpa only [basisWeights, List.length_ofFn] using i.isLt

/-- Distinct deleted vertices give distinct normalized boundary bases. -/
theorem deleteVertex_injective {m p : ℕ} (b : Basis m (p+1)) :
    Function.Injective (deleteVertex b) := by
  intro i j he
  by_contra hne
  obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hne
  have hb := congrArg (fun c : Basis m p => c z) he
  change b (i.succAbove z) = b (j.succAbove z) at hb
  have h := b.injective hb
  rw [hz] at h
  exact Fin.succAbove_ne i z h

/-- The coefficient of a literal face is exactly its alternating sign. -/
theorem differentialBasis_face {m p : ℕ} (b : Basis m (p+1)) (i : Fin (p+2)) :
    differentialBasis m p b (deleteVertex b i) = (-1 : ℤ)^i.val := by
  classical
  unfold differentialBasis
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · exact Finsupp.single_eq_same
  · intro j _ hji
    exact Finsupp.single_eq_of_ne (fun h => hji ((deleteVertex_injective b h).symm))
  · simp

/-- Every nonzero boundary entry has an explicit deleted-vertex witness. -/
theorem exists_deleteVertex_of_boundary_ne_zero {m p : ℕ} (b : Basis m (p+1))
    (c : Basis m p) (hc : differentialBasis m p b c ≠ 0) :
    ∃ i, deleteVertex b i = c := by
  classical
  by_contra hn
  apply hc
  unfold differentialBasis
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact Finsupp.single_eq_of_ne (fun he => hn ⟨i, he.symm⟩)

/-- The boundary incidence matrix is strictly ordered by the concrete height. -/
theorem boundary_signed_height {m p : ℕ} (b : Basis m (p+1)) (c : Basis m p)
    (hc : differentialBasis m p b c ≠ 0) :
    0 < differentialBasis m p b c * (basisHeight c - basisHeight b) := by
  obtain ⟨i, rfl⟩ := exists_deleteVertex_of_boundary_ne_zero b c hc
  rw [differentialBasis_face]
  exact basisHeight_deleteVertex b i

theorem negative_boundary_height {m p : ℕ} (b : Basis m (p+1)) (c : Basis m p)
    (hc : differentialBasis m p b c < 0) : basisHeight c < basisHeight b := by
  have hh := boundary_signed_height b c (ne_of_lt hc)
  rcases mul_pos_iff.mp hh with h | h
  · exact False.elim ((not_lt_of_ge hc.le) h.1)
  · omega

theorem positive_boundary_height {m p : ℕ} (b : Basis m (p+1)) (c : Basis m p)
    (hc : 0 < differentialBasis m p b c) : basisHeight b < basisHeight c := by
  have hh := boundary_signed_height b c (ne_of_gt hc)
  rcases mul_pos_iff.mp hh with h | h
  · omega
  · exact False.elim ((not_lt_of_ge hc.le) h.1)

end Thomason.Construction.SimplexComplex

end

section

/-! # Stationary deformation inclusions are actual weak equivalences

A strict retraction and a homotopy stationary on its image give inverses on
components and based homotopy groups. This is the topological semantic
bridge needed for stationary Street/Gray prisms; no KQ axiom is used.
-/

namespace Thomason.Construction

open CategoryTheory

universe u

namespace HomotopyMaps

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- Composition with explicit basepoint equalities. -/
theorem basedGroupMap_comp (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z} (ef : f x = y) (eg : g y = z) (n : ℕ) :
    basedGroupMap (g.comp f) ((congrArg g ef).trans eg) n =
      basedGroupMap g eg n ∘ basedGroupMap f ef n := by
  funext a
  induction a using Quotient.inductionOn with
  | h p =>
    apply congrArg (Quotient.mk _)
    apply GenLoop.ext
    intro t
    rfl

@[simp]
theorem basedGroupMap_id {X : Type u} [TopologicalSpace X] (x : X) (n : ℕ) :
    basedGroupMap (ContinuousMap.id X) (x := x) rfl n = id := groupMap_id n x

end HomotopyMaps

/-- A stationary deformation retraction gives a weak equivalence on its
inclusion, proved using the actual loop quotients at every source basepoint. -/
theorem weakEquivalence_of_strongDeformationRetract
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (i : C(X, Y)) (r : C(Y, X)) (hi : r.comp i = ContinuousMap.id X)
    (H : (i.comp r).HomotopyRel (ContinuousMap.id Y) (Set.range i)) :
    IsWeakHomotopyEquivalence i := by
  constructor
  · have hl : Function.LeftInverse (HomotopyMaps.componentsMap r)
        (HomotopyMaps.componentsMap i) := by
      intro a
      change (HomotopyMaps.componentsMap r ∘ HomotopyMaps.componentsMap i) a = a
      rw [← HomotopyMaps.componentsMap_comp, hi, HomotopyMaps.componentsMap_id]
      rfl
    have hr : Function.RightInverse (HomotopyMaps.componentsMap r)
        (HomotopyMaps.componentsMap i) := by
      intro a
      change (HomotopyMaps.componentsMap i ∘ HomotopyMaps.componentsMap r) a = a
      rw [← HomotopyMaps.componentsMap_comp,
        HomotopyMaps.componentsMap_homotopy H.toHomotopy, HomotopyMaps.componentsMap_id]
      rfl
    exact ⟨hl.injective, hr.surjective⟩
  · intro n x
    have hx : r (i x) = x := congrFun (congrArg DFunLike.coe hi) x
    let j := HomotopyMaps.basedGroupMap r hx (n+1)
    have hl : Function.LeftInverse j (HomotopyMaps.groupMap i (n+1) x) := by
      intro a
      change (HomotopyMaps.basedGroupMap r hx (n+1) ∘
        HomotopyMaps.basedGroupMap i rfl (n+1)) a = a
      rw [← HomotopyMaps.basedGroupMap_comp]
      induction a using Quotient.inductionOn with
      | h p =>
        apply congrArg (Quotient.mk _)
        apply GenLoop.ext
        intro t
        exact congrFun (congrArg DFunLike.coe hi) (p t)
    have Hx : (i.comp r).HomotopyRel (ContinuousMap.id Y) {i x} := {
      toHomotopy := H.toHomotopy
      prop' := fun t y hy => H.eq_fst t (by
        have hy' : y = i x := Set.mem_singleton_iff.mp hy
        exact ⟨x, hy'.symm⟩) }
    have hr : Function.RightInverse j (HomotopyMaps.groupMap i (n+1) x) := by
      intro a
      change (HomotopyMaps.basedGroupMap i rfl (n+1) ∘
        HomotopyMaps.basedGroupMap r hx (n+1)) a = a
      rw [← HomotopyMaps.basedGroupMap_comp]
      exact (congrFun (HomotopyMaps.basedGroupMap_homotopy Hx
        (congrArg i hx) rfl (n+1)) a).trans
          (congrFun (HomotopyMaps.basedGroupMap_id (i x) (n+1)) a)
    exact ⟨hl.injective, hr.surjective⟩

end Thomason.Construction

end

section

/-! # The actual weak homotopy type of finite topological simplices

Straight-line homotopies contract every generalized loop while fixing its
boundary. Thus the semantic weak-equivalence test holds for all maps
between nonempty finite simplices, without Kan–Quillen assumptions.
-/

namespace Thomason.Construction

open Convexity

namespace HomotopyMaps

universe u v

variable {M : Type u} [Finite M]

/-- The explicit straight-line nullhomotopy of a based simplex-valued loop. -/
noncomputable def simplexLoopContraction (x : StdSimplex ℝ M) {N : Type v}
    (p : GenLoop N (StdSimplex ℝ M) x) :
    p.val.HomotopyRel (GenLoop.const (N := N) (x := x)).val (Cube.boundary N) where
  toFun tz := convexCombPair (R := ℝ) (unitInterval.symm tz.1) tz.1
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) (p tz.2) x
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ M).continuous_iff]
    apply continuous_pi
    intro k
    simp only [Function.comp_def, StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      unitInterval.coe_symm_eq]
    fun_prop
  map_zero_left z := by
    ext k
    simp
  map_one_left z := by
    ext k
    simp
  prop' t z hz := by
    change convexCombPair (R := ℝ) _ _ _ _ _ (p z) x = p z
    have hp : p z = x := p.property z hz
    rw [hp]
    ext k
    simp only [StdSimplex.weights_convexCombPair, Finsupp.coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitInterval.coe_symm_eq]
    ring

/-- Every positive-dimensional homotopy group of a finite simplex is trivial. -/
instance simplex_homotopyGroup_subsingleton (x : StdSimplex ℝ M) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi n (StdSimplex ℝ M) x) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      apply Quotient.sound
      exact (show GenLoop.Homotopic p GenLoop.const from ⟨simplexLoopContraction x p⟩).trans
        (show GenLoop.Homotopic q GenLoop.const from ⟨simplexLoopContraction x q⟩).symm

end HomotopyMaps

/-- All continuous maps between nonempty finite topological simplices pass
the actual component and homotopy-group weak-equivalence test. -/
theorem simplex_isWeakHomotopyEquivalence {M N : Type} [Finite M] [Finite N]
    [Nonempty M] [Nonempty N] (f : C(StdSimplex ℝ M, StdSimplex ℝ N)) :
    IsWeakHomotopyEquivalence f := by
  constructor
  · exact Function.bijective_of_subsingleton' _
  · intro n x
    exact Function.bijective_of_subsingleton' _

end Thomason.Construction

end

section

/-! # The Kan–Quillen weak-equivalence test on actual representable maps

The comparison with topological simplices is Mathlib's actual realization
isomorphism. The weak-equivalence assertion follows from explicit based
contractions of these simplices, without a model structure.
-/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

/-- Each map of topological standard simplices is weak, including the
universe-lifted spaces used by the realization functor. -/
theorem simplexCategory_toTop_map_weak {n m : SimplexCategory} (f : n ⟶ m) :
    topologicalWeakEquivalences (SimplexCategory.toTop.{0}.map f) := by
  let X := SimplexCategory.toTop₀.obj n
  let Y := SimplexCategory.toTop₀.obj m
  let a := SimplexCategory.toTop₀.map f
  let i := (TopCat.isoOfHomeo (X.uliftFunctorObjHomeo.{0})).hom
  let j := (TopCat.isoOfHomeo (Y.uliftFunctorObjHomeo.{0})).hom
  have ha : topologicalWeakEquivalences a :=
    simplex_isWeakHomotopyEquivalence a.hom
  have hi : IsIso i := by dsimp [i]; infer_instance
  have hj : IsIso j := by dsimp [j]; infer_instance
  have hn : i ≫ TopCat.uliftFunctor.{0,0}.map a = a ≫ j := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  change topologicalWeakEquivalences (TopCat.uliftFunctor.{0,0}.map a)
  apply (topologicalWeakEquivalences.cancel_left_of_respectsIso i _).mp
  rw [hn]
  exact topologicalWeakEquivalences.comp_mem _ _ ha
    (topologicalWeakEquivalences.of_isIso j)

/-- Realization sends every ordinal-induced map of representables to a weak
homotopy equivalence. -/
theorem realized_simplex_map_weak {n m : SimplexCategory} (f : n ⟶ m) :
    realizationWeakEquivalences (SSet.stdSimplex.{0}.map f) := by
  let F := SSet.stdSimplex.{0} ⋙ SSet.toTop
  let e := SSet.toTopSimplex.{0}
  have hn := e.hom.naturality f
  change topologicalWeakEquivalences (F.map f)
  have he : IsIso (e.hom.app m) := by dsimp [e]; infer_instance
  apply (topologicalWeakEquivalences.cancel_right_of_respectsIso _ (e.hom.app m)).mp
  rw [hn]
  exact topologicalWeakEquivalences.comp_mem _ _
    (topologicalWeakEquivalences.of_isIso (e.hom.app n))
    (simplexCategory_toTop_map_weak f)

end Thomason.Construction

end

end OAI
