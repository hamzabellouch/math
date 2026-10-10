import OAI.CategoryTheory.Thomason.Chains.SimplexBasisHeight
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeUniversal
import OAI.CategoryTheory.Thomason.Simplicial.RealizedSimplexWeakEquivalences
import Mathlib.Data.Nat.Bits

namespace OAI

section

/-! # The upper atom of a one-generator expression

An expression containing exactly one atom of degree greater than r maps
to that atom above r. Lower-dimensional whiskering changes no such table
entry. No assumption on the expression's composition levels is needed.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open CategoryTheory StrictOmegaCategory StrictOmegaCategory.ExpressionDegree

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

private theorem mapped_comp_table_left_bounded {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) {x y : C} {r s n : ℕ}
    (hxy : C.target s x = C.source s y) (hs : s ≤ r)
    (hx : C.DimensionLE r x) (hn : r < n) (side : Bool) :
    (F.toFun (C.comp s x y hxy)).table side n = (F.toFun y).table side n := by
  have hf : K.realization.target s (F.toFun x) = K.realization.source s (F.toFun y) :=
    (F.map_face true s x).symm.trans
      ((congrArg F.toFun hxy).trans (F.map_face false s y))
  have he := congrArg (fun z : Cell K => z.table side n) (F.map_comp s x y hxy hf)
  have hz := Cell.table_zero_of_dimensionLE (F.dimensionLE hx) hn side
  refine he.trans ?_
  change Cell.pasteTable (F.toFun x) (F.toFun y) s side n = (F.toFun y).table side n
  simp only [Cell.pasteTable, Nat.not_lt.mpr (hs.trans hn.le),
    Nat.ne_of_gt (hs.trans_lt hn), ite_false, hz, zero_add]

private theorem mapped_comp_table_right_bounded {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) {x y : C} {r s n : ℕ}
    (hxy : C.target s x = C.source s y) (hs : s ≤ r)
    (hy : C.DimensionLE r y) (hn : r < n) (side : Bool) :
    (F.toFun (C.comp s x y hxy)).table side n = (F.toFun x).table side n := by
  have hf : K.realization.target s (F.toFun x) = K.realization.source s (F.toFun y) :=
    (F.map_face true s x).symm.trans
      ((congrArg F.toFun hxy).trans (F.map_face false s y))
  have he := congrArg (fun z : Cell K => z.table side n) (F.map_comp s x y hxy hf)
  have hz := Cell.table_zero_of_dimensionLE (F.dimensionLE hy) hn side
  refine he.trans ?_
  change Cell.pasteTable (F.toFun x) (F.toFun y) s side n = (F.toFun x).table side n
  simp only [Cell.pasteTable, Nat.not_lt.mpr (hs.trans hn.le),
    Nat.ne_of_gt (hs.trans_lt hn), ite_false, hz, add_zero]

/-- The unique higher occurrence in an expression supplies its actual
positive upper atom. The occurrence itself is retained in the conclusion. -/
theorem expression_upper_atom {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ a, F.toFun (g a) = B.atomCell a)
    (hd : ∀ a, C.DimensionLE a.1 (g a))
    {x : C} (t : CompositionExpression C g x) (r : ℕ)
    (ht : highCount (fun a : B.AtomIndex => a.1) r t.labels = 1) :
    ∃ a ∈ t.labels, r < a.1 ∧
      ∀ n, r < n → ∀ side, (F.toFun x).table side n = (B.atomCell a).table side n := by
  induction t with
  | generator a =>
    have ha : r < a.1 := by
      by_contra ha
      simp [CompositionExpression.labels, highCount, ha] at ht
    exact ⟨a, by simp [CompositionExpression.labels], ha, fun n _ side =>
      congrArg (fun z : Cell K => z.table side n) (hg a)⟩
  | @comp x y s hxy tx ty ihx ihy =>
    have hsum : highCount (fun a : B.AtomIndex => a.1) r tx.labels +
        highCount (fun a : B.AtomIndex => a.1) r ty.labels = 1 := by
      simpa only [CompositionExpression.labels, highCount_append] using ht
    by_cases hzero : highCount (fun a : B.AtomIndex => a.1) r tx.labels = 0
    · have hone : highCount (fun a : B.AtomIndex => a.1) r ty.labels = 1 := by omega
      obtain ⟨a, ha, har, hupper⟩ := ihy hone
      refine ⟨a, List.mem_append_right _ ha, har, ?_⟩
      have hxr : C.DimensionLE r x := tx.dimensionLE (fun a => a.1) hd r
        ((highCount_eq_zero_iff _ r tx.labels).mp hzero)
      by_cases hs : s ≤ r
      · intro n hn side
        exact (mapped_comp_table_left_bounded F hxy hs hxr hn side).trans (hupper n hn side)
      · have he := C.comp_of_dimensionLE (show r ≤ s by omega) hxr hxy
        intro n hn side
        exact (congrArg (fun z => (F.toFun z).table side n) he).trans (hupper n hn side)
    · have hone : highCount (fun a : B.AtomIndex => a.1) r tx.labels = 1 := by omega
      have hzero' : highCount (fun a : B.AtomIndex => a.1) r ty.labels = 0 := by omega
      obtain ⟨a, ha, har, hupper⟩ := ihx hone
      refine ⟨a, List.mem_append_left _ ha, har, ?_⟩
      have hyr : C.DimensionLE r y := ty.dimensionLE (fun a => a.1) hd r
        ((highCount_eq_zero_iff _ r ty.labels).mp hzero')
      by_cases hs : s ≤ r
      · intro n hn side
        exact (mapped_comp_table_right_bounded F hxy hs hyr hn side).trans (hupper n hn side)
      · have he := comp_eq_left_of_dimensionLE s hxy
          (C.dimensionLE_mono (show r ≤ s by omega) hyr)
        intro n hn side
        exact (congrArg (fun z => (F.toFun z).table side n) he).trans (hupper n hn side)

theorem expression_aboveAtomOrZero {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ a, F.toFun (g a) = B.atomCell a)
    (hd : ∀ a, C.DimensionLE a.1 (g a))
    {x : C} (t : CompositionExpression C g x) (r : ℕ)
    (ht : highCount (fun a : B.AtomIndex => a.1) r t.labels = 1) :
    B.AboveAtomOrZero r (F.toFun x) := by
  obtain ⟨a, _, ha, hupper⟩ := B.expression_upper_atom g F hg hd t r ht
  exact Or.inr ⟨a, ha, hupper⟩

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # The finite ordered basis of two composable globes

The right copy uses the left copy for every shared lower face and for its
source in the gluing dimension. The remaining basis elements are distinct.
The integer height below places every negative boundary before its cell and
every positive boundary after it. This is the concrete order needed for
positive-table decomposition; no generation assertion is assumed here.
-/

namespace Thomason.Construction.PastingGlobeBasis

open DirectedGlobeComplex

/-- A canonical representative of a basis element of two n-globes pasted
along a k-face. `false` denotes the left globe. -/
abbrev Basis (n k p : ℕ) :=
  {b : Bool × Bool //
    (p < n ∨ (p = n ∧ b.2 = false)) ∧
    (b.1 = false ∨ k < p ∨ (p = k ∧ b.2 = true))}

abbrev Chains (n k p : ℕ) := Basis n k p →₀ ℤ

/-- The left globe supplies the chosen representatives of shared faces. -/
def left {n k p : ℕ} (b : DirectedGlobeComplex.Basis n p) : Basis n k p :=
  ⟨(false, b.val), b.property, Or.inl rfl⟩

/-- Normalize a right-globe face to its canonical representative. -/
def right {n k p : ℕ} (hkn : k < n) (b : DirectedGlobeComplex.Basis n p) :
    Basis n k p :=
  if hp : p < k then left b
  else if he : p = k then
    if ha : b.val = false then left ⟨true, Or.inl (he ▸ hkn)⟩
    else ⟨(true, b.val), b.property, Or.inr (Or.inr ⟨he, Bool.eq_true_of_not_eq_false ha⟩)⟩
  else ⟨(true, b.val), b.property, Or.inr (Or.inl (by omega))⟩

@[simp] theorem right_below {n k p : ℕ} (hkn : k < n)
    (b : DirectedGlobeComplex.Basis n p) (hp : p < k) :
    right hkn b = left b := by simp [right, hp]

@[simp] theorem right_source {n k : ℕ} (hkn : k < n) :
    right hkn (⟨false, Or.inl hkn⟩ : DirectedGlobeComplex.Basis n k) =
      left (⟨true, Or.inl hkn⟩ : DirectedGlobeComplex.Basis n k) := by
  simp [right]

/-- The dimension bound follows from the basis itself. -/
theorem degree_le {n k p : ℕ} (b : Basis n k p) : p ≤ n := by
  rcases b.property.1 with h | ⟨h, _⟩ <;> omega

/-- Each canonical basis element comes from one of the two globe bases. -/
theorem left_or_right {n k p : ℕ} (hkn : k < n) (b : Basis n k p) :
    (∃ a : DirectedGlobeComplex.Basis n p, left a = b) ∨
      (∃ a : DirectedGlobeComplex.Basis n p, right hkn a = b) := by
  rcases b with ⟨⟨s, a⟩, hv, hs⟩
  cases s with
  | false => exact Or.inl ⟨⟨a, hv⟩, rfl⟩
  | true =>
    right
    refine ⟨⟨a, hv⟩, ?_⟩
    rcases hs with hs | hs | ⟨he, ha⟩
    · cases hs
    · simp [right, Nat.not_lt.mpr hs.le, Nat.ne_of_gt hs]
    · subst p
      have ha' : a = true := ha
      subst a
      simp [right]

/-- Every positive-dimensional basis element has two canonical boundary bases. -/
def face {n k p : ℕ} (hkn : k < n) (a : Bool) (b : Basis n k (p+1)) :
    Basis n k p :=
  let hpn : p < n := by have := degree_le b; omega
  if b.val.1 then right hkn ⟨a, Or.inl hpn⟩ else left ⟨a, Or.inl hpn⟩

/-- Source and target of every boundary basis have the same lower faces. -/
theorem face_globular {n k p : ℕ} (hkn : k < n) (a c : Bool)
    (b : Basis n k (p+2)) :
    face hkn a (face hkn false b) = face hkn a (face hkn c b) := by
  cases c with
  | false => rfl
  | true =>
    rcases b with ⟨⟨s, t⟩, hv, hs⟩
    cases s with
    | false => rfl
    | true =>
      by_cases hp : p+1 < k
      · simp [face, right, left, hp]
      · by_cases he : p+1 = k
        · simp [face, right, left, he, show p < k by omega]
        · simp [face, right, left, hp, he]

/-- Negative and positive boundary, with no cancellation between them. -/
noncomputable def boundary {n k p : ℕ} (hkn : k < n) (b : Basis n k (p+1)) :
    Chains n k p :=
  Finsupp.single (face hkn true b) 1 - Finsupp.single (face hkn false b) 1


/-- Differential on the free abelian groups of canonical bases. -/
noncomputable def differential {n k : ℕ} (hkn : k < n) (p : ℕ) :
    Chains n k (p+1) →ₗ[ℤ] Chains n k p :=
  Finsupp.linearCombination ℤ (boundary hkn)

@[simp] theorem differential_single {n k p : ℕ} (hkn : k < n)
    (b : Basis n k (p+1)) (z : ℤ) :
    differential hkn p (Finsupp.single b z) = z • boundary hkn b := by
  simp [differential]

@[simp] theorem differential_boundary {n k p : ℕ} (hkn : k < n)
    (b : Basis n k (p+2)) :
    differential hkn p (boundary hkn b) = 0 := by
  simp only [boundary, map_sub, differential_single, one_smul]
  rw [face_globular hkn true true b, face_globular hkn false true b]
  simp

/-- Globularity proves that the explicit boundary squares to zero. -/
theorem differential_squared {n k : ℕ} (hkn : k < n) (p : ℕ)
    (x : Chains n k (p+2)) :
    differential hkn p (differential hkn (p+1) x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b z => simp

noncomputable def weight (n k p : ℕ) : Chains n k p →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => 1)

@[simp] theorem weight_single {n k p : ℕ} (b : Basis n k p) (z : ℤ) :
    weight n k p (Finsupp.single b z) = z := by simp [weight]

@[simp] theorem weight_differential {n k : ℕ} (hkn : k < n) (p : ℕ)
    (x : Chains n k (p+1)) : weight n k p (differential hkn p x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b z => simp [boundary]

def positive (n k p : ℕ) : AddSubmonoid (Chains n k p) where
  carrier := {x | ∀ b, 0 ≤ x b}
  zero_mem' := fun _ => le_rfl
  add_mem' hx hy b := add_nonneg (hx b) (hy b)

/-- The concrete directed complex of the pasted pair, before tensoring. -/
noncomputable def complex (n k : ℕ) (hkn : k < n) : DirectedComplex where
  group p := AddCommGrpCat.of (Chains n k p)
  differential p := (differential hkn p).toAddMonoidHom
  differential_squared := differential_squared hkn
  augmentation := (weight n k 0).toAddMonoidHom
  augmentation_differential := weight_differential hkn 0
  positive := positive n k

/-- A global height on all dimensions of the pasted-globe basis. -/
def height {n k p : ℕ} (b : Basis n k p) : ℤ :=
  if b.val.1 then
    if b.val.2 then 4*(n:ℤ)-2*k-p else 2*(n:ℤ)-2*k+p
  else if b.val.2 then
    if p < k then 4*(n:ℤ)-2*k-p else 2*(n:ℤ)-p
  else p

/-- Every negative incidence strictly decreases the global height. -/
theorem height_source_lt {n k p : ℕ} (hkn : k < n) (b : Basis n k (p+1)) :
    height (face hkn false b) < height b := by
  rcases b with ⟨⟨s, a⟩, hv, hs⟩
  cases s <;> cases a
  all_goals
    simp_all [face, right, left, height]
    all_goals first | omega | (split_ifs <;> simp_all <;> omega)

/-- Every positive incidence strictly increases the global height. -/
theorem height_lt_target {n k p : ℕ} (hkn : k < n) (b : Basis n k (p+1)) :
    height b < height (face hkn true b) := by
  rcases b with ⟨⟨s, a⟩, hv, hs⟩
  cases s <;> cases a
  all_goals
    simp_all [face, right, left, height]
    all_goals first | omega | (split_ifs <;> simp_all <;> omega)

/-- Distinct signs of a boundary never overlap in this basis. -/
theorem face_ne {n k p : ℕ} (hkn : k < n) (b : Basis n k (p+1)) :
    face hkn false b ≠ face hkn true b := by
  intro he
  have hs := height_source_lt hkn b
  have ht := height_lt_target hkn b
  rw [he] at hs
  omega

/-- The order controls the actual negative coefficients of the boundary. -/
theorem height_lt_of_boundary_neg {n k p : ℕ} (hkn : k < n)
    (b : Basis n k (p+1)) (c : Basis n k p) (hc : boundary hkn b c < 0) :
    height c < height b := by
  classical
  by_cases hs : face hkn false b = c
  · subst c
    exact height_source_lt hkn b
  · simp only [boundary, Finsupp.sub_apply, Finsupp.single_apply, hs, ite_false,
      sub_zero] at hc
    split_ifs at hc <;> omega

/-- The order controls the actual positive coefficients of the boundary. -/
theorem height_lt_of_boundary_pos {n k p : ℕ} (hkn : k < n)
    (b : Basis n k (p+1)) (c : Basis n k p) (hc : 0 < boundary hkn b c) :
    height b < height c := by
  classical
  by_cases ht : face hkn true b = c
  · subst c
    exact height_lt_target hkn b
  · simp only [boundary, Finsupp.sub_apply, Finsupp.single_apply, ht, ite_false] at hc
    split_ifs at hc <;> omega

end Thomason.Construction.PastingGlobeBasis

end

section

/-! # The two globe inclusions in the explicit pasted basis

These are positive chain maps into the ordered complex, with the shared
faces identified literally. Their construction precedes the universal
property comparison with the abelianization of the strict pasted globe.
-/

namespace Thomason.Construction.PastingGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- Choose the left or right inclusion of a globe basis. -/
def embed {n k p : ℕ} (hkn : k < n) (s : Bool)
    (b : DirectedGlobeComplex.Basis n p) : Basis n k p :=
  if s then right hkn b else left b

/-- Both inclusions preserve the two boundary faces. -/
theorem face_embed {n k p : ℕ} (hkn : k < n) (s a : Bool)
    (b : DirectedGlobeComplex.Basis n (p+1)) :
    face hkn a (embed hkn s b) =
      embed hkn s ⟨a, Or.inl (by rcases b.property with h | ⟨h, _⟩ <;> omega)⟩ := by
  cases s with
  | false => rfl
  | true =>
    by_cases hp : p+1 < k
    · simp [embed, right, hp, face, left, show p < k by omega]
    · by_cases he : p+1 = k
      · simp [embed, right, he, face, left, show p < k by omega]
      · simp [embed, right, hp, he, face, left]

/-- Extend a basis inclusion linearly. -/
def embedApp {n k : ℕ} (hkn : k < n) (s : Bool) (p : ℕ) :
    DirectedGlobeComplex.Chains n p →ₗ[ℤ] Chains n k p :=
  Finsupp.linearCombination ℤ (fun b => Finsupp.single (embed hkn s b) 1)

@[simp] theorem embedApp_single {n k p : ℕ} (hkn : k < n) (s : Bool)
    (b : DirectedGlobeComplex.Basis n p) (z : ℤ) :
    embedApp hkn s p (Finsupp.single b z) = Finsupp.single (embed hkn s b) z := by
  simp [embedApp]

/-- The free inclusions commute with the actual chain differentials. -/
theorem embedApp_differential {n k : ℕ} (hkn : k < n) (s : Bool) (p : ℕ)
    (u : DirectedGlobeComplex.Chains n (p+1)) :
    embedApp hkn s p (DirectedGlobeComplex.differential n p u) =
      differential hkn p (embedApp hkn s (p+1) u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z =>
    have hp : p < n := by rcases b.property with h | ⟨h, _⟩ <;> omega
    simp only [DirectedGlobeComplex.differential_single, map_smul,
      DirectedGlobeComplex.boundary, dite_eq_left hp, map_sub, embedApp_single,
      differential_single, boundary, face_embed]

/-- Augmentation is unchanged by either inclusion. -/
theorem embedApp_augmentation {n k : ℕ} (hkn : k < n) (s : Bool)
    (u : DirectedGlobeComplex.Chains n 0) :
    weight n k 0 (embedApp hkn s 0 u) = DirectedGlobeComplex.weight n 0 u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z => simp

/-- Every coefficient of an included positive chain remains nonnegative. -/
theorem embedApp_positive {n k p : ℕ} (hkn : k < n) (s : Bool)
    (u : DirectedGlobeComplex.Chains n p) (hu : u ∈ DirectedGlobeComplex.positive n p) :
    embedApp hkn s p u ∈ positive n k p := by
  classical
  change (u.sum fun b z => z • Finsupp.single (embed hkn s b) 1) ∈ positive n k p
  apply (positive n k p).sum_mem
  intro b hb
  change u b • Finsupp.single (embed hkn s b) 1 ∈ positive n k p
  rw [← Int.toNat_of_nonneg (hu b), natCast_zsmul]
  apply (positive n k p).nsmul_mem
  intro c
  simp only [Finsupp.single_apply]
  split_ifs <;> norm_num

/-- The two actual positive chain inclusions into the pasted basis complex. -/
def inclusion {n k : ℕ} (hkn : k < n) (s : Bool) :
    Hom (DirectedGlobeComplex.complex n) (complex n k hkn) where
  app p := (embedApp hkn s p).toAddMonoidHom
  differential := embedApp_differential hkn s
  augmentation := embedApp_augmentation hkn s
  positive _ _ hu := embedApp_positive hkn s _ hu

end

end Thomason.Construction.PastingGlobeBasis

end

section

/-! # The explicit chain basis of four globes in an interchange square

Each row has the already constructed two-globe basis. Below the vertical
gluing dimension the rows coincide, and in that dimension the source of
the second row is the target of the first. No realization-colimit assertion
is used in this construction.
-/

namespace Thomason.Construction.GridGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

abbrev Basis (n k l p : ℕ) :=
  {b : Bool × PastingGlobeBasis.Basis n k p //
    b.1 = false ∨ l < p ∨ (p = l ∧ b.2.val.2 = true)}

abbrev Chains (n k l p : ℕ) := Basis n k l p →₀ ℤ

def left {n k l p : ℕ} (b : PastingGlobeBasis.Basis n k p) : Basis n k l p :=
  ⟨(false, b), Or.inl rfl⟩

def targetBasis {n k l p : ℕ} (hkl : k < l) (hln : l < n)
    (b : PastingGlobeBasis.Basis n k p) (hp : p = l) : PastingGlobeBasis.Basis n k p :=
  ⟨(b.val.1, true), Or.inl (hp ▸ hln), Or.inr (Or.inl (hp ▸ hkl))⟩

def embed {n k l p : ℕ} (hkl : k < l) (hln : l < n) (s : Bool)
    (b : PastingGlobeBasis.Basis n k p) : Basis n k l p :=
  if s then
    if hp : p < l then left b
    else if he : p = l then
      if hb : b.val.2 = false then left (targetBasis hkl hln b he)
      else ⟨(true, b), Or.inr (Or.inr ⟨he, Bool.eq_true_of_not_eq_false hb⟩)⟩
    else ⟨(true, b), Or.inr (Or.inl (by omega))⟩
  else left b

theorem degree_le {n k l p : ℕ} (b : Basis n k l p) : p ≤ n :=
  PastingGlobeBasis.degree_le b.val.2

theorem embed_self {n k l p : ℕ} (hkl : k < l) (hln : l < n)
    (b : Basis n k l p) : embed hkl hln b.val.1 b.val.2 = b := by
  rcases b with ⟨⟨s, b⟩, hs⟩
  cases s with
  | false => rfl
  | true =>
    rcases hs with hs | hp | ⟨he, ha⟩
    · cases hs
    · simp [embed, Nat.not_lt.mpr hp.le, Nat.ne_of_gt hp]
    · have ha' : b.val.2 = true := ha
      simp [embed, he, ha']

def face {n k l p : ℕ} (hkl : k < l) (hln : l < n) (a : Bool)
    (b : Basis n k l (p+1)) : Basis n k l p :=
  embed hkl hln b.val.1 (PastingGlobeBasis.face (hkl.trans hln) a b.val.2)

theorem face_embed {n k l p : ℕ} (hkl : k < l) (hln : l < n) (s a : Bool)
    (b : PastingGlobeBasis.Basis n k (p+1)) :
    face hkl hln a (embed hkl hln s b) =
      embed hkl hln s (PastingGlobeBasis.face (hkl.trans hln) a b) := by
  cases s with
  | false => rfl
  | true =>
    by_cases hp : p+1 < l
    · simp [embed, face, left, hp, show p < l by omega]
    · by_cases he : p+1 = l
      · by_cases hb : b.val.2 = false
        all_goals simp [embed, face, he, hb, targetBasis, left,
          show p < l by omega, PastingGlobeBasis.face]
      · simp [embed, face, hp, he]

theorem face_globular {n k l p : ℕ} (hkl : k < l) (hln : l < n) (a c : Bool)
    (b : Basis n k l (p+2)) :
    face hkl hln a (face hkl hln false b) = face hkl hln a (face hkl hln c b) := by
  change face hkl hln a (embed hkl hln b.val.1
      (PastingGlobeBasis.face (hkl.trans hln) false b.val.2)) =
    face hkl hln a (embed hkl hln b.val.1
      (PastingGlobeBasis.face (hkl.trans hln) c b.val.2))
  rw [face_embed, face_embed, PastingGlobeBasis.face_globular]

noncomputable def boundary {n k l p : ℕ} (hkl : k < l) (hln : l < n)
    (b : Basis n k l (p+1)) : Chains n k l p :=
  Finsupp.single (face hkl hln true b) 1 - Finsupp.single (face hkl hln false b) 1

noncomputable def differential {n k l : ℕ} (hkl : k < l) (hln : l < n) (p : ℕ) :
    Chains n k l (p+1) →ₗ[ℤ] Chains n k l p :=
  Finsupp.linearCombination ℤ (boundary hkl hln)

@[simp] theorem differential_single {n k l p : ℕ} (hkl : k < l) (hln : l < n)
    (b : Basis n k l (p+1)) (z : ℤ) :
    differential hkl hln p (Finsupp.single b z) = z • boundary hkl hln b := by
  simp [differential]

@[simp] theorem differential_boundary {n k l p : ℕ} (hkl : k < l) (hln : l < n)
    (b : Basis n k l (p+2)) : differential hkl hln p (boundary hkl hln b) = 0 := by
  simp only [boundary, map_sub, differential_single, one_smul]
  rw [face_globular hkl hln true true b, face_globular hkl hln false true b]
  simp

theorem differential_squared {n k l : ℕ} (hkl : k < l) (hln : l < n) (p : ℕ)
    (x : Chains n k l (p+2)) :
    differential hkl hln p (differential hkl hln (p+1) x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b z => simp

noncomputable def weight (n k l p : ℕ) : Chains n k l p →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => 1)

@[simp] theorem weight_single {n k l p : ℕ} (b : Basis n k l p) (z : ℤ) :
    weight n k l p (Finsupp.single b z) = z := by simp [weight]

@[simp] theorem weight_differential {n k l : ℕ} (hkl : k < l) (hln : l < n) (p : ℕ)
    (x : Chains n k l (p+1)) : weight n k l p (differential hkl hln p x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b z => simp [boundary]

def positive (n k l p : ℕ) : AddSubmonoid (Chains n k l p) where
  carrier := {x | ∀ b, 0 ≤ x b}
  zero_mem' := fun _ => le_rfl
  add_mem' hx hy b := add_nonneg (hx b) (hy b)

noncomputable def complex {n k l : ℕ} (hkl : k < l) (hln : l < n) : DirectedComplex where
  group p := AddCommGrpCat.of (Chains n k l p)
  differential p := (differential hkl hln p).toAddMonoidHom
  differential_squared := differential_squared hkl hln
  augmentation := (weight n k l 0).toAddMonoidHom
  augmentation_differential := weight_differential hkl hln 0
  positive := positive n k l

def height {n k l p : ℕ} (b : Basis n k l p) : ℤ :=
  let offset : ℤ := if b.val.2.val.1 then 4*(n:ℤ)-2*l-2*k else 0
  if b.val.2.val.2 then
    if p < k then 8*(n:ℤ)-4*l-2*k-p
    else offset + if b.val.1 then 4*(n:ℤ)-2*l-p
      else if p < l then 4*(n:ℤ)-2*l-p else 2*(n:ℤ)-p
  else offset + if b.val.1 then 2*(n:ℤ)-2*l+p else p

end Thomason.Construction.GridGlobeBasis

end

section

/-! # The positive universal map from the pasted-globe basis

A pair of matching positive cell tables gives an actual positive chain map
from the explicit pasted complex. The formula reads each canonical basis
in the corresponding table; matching identifies exactly the shared faces.
-/

namespace Thomason.Construction.PastingGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex CategoryTheory

noncomputable section

variable {L : DirectedComplex.{0}}

/-- The value of a canonical basis in a pair of cell tables. -/
def value {n k p : ℕ} (x y : Cell L) (b : Basis n k p) : L.group p :=
  if b.val.1 then y.table b.val.2 p else x.table b.val.2 p

/-- Matching cell tables give the same value on every shared representative. -/
theorem value_embed {n k p : ℕ} (hkn : k < n) (x y : Cell L)
    (hxy : x.face true k = y.face false k) (s : Bool)
    (b : DirectedGlobeComplex.Basis n p) :
    value x y (embed hkn s b) = (if s then y else x).table b.val p := by
  cases s with
  | false => rfl
  | true =>
    change value x y (right hkn b) = y.table b.val p
    by_cases hp : p < k
    · simpa only [right, dite_eq_left hp, value, left, Bool.false_eq_true, ite_false] using
        Cell.matching_below hxy b.val hp
    · by_cases he : p = k
      · subst p
        by_cases ha : b.val = false
        · simpa [right, ha, value, left] using Cell.matching_top hxy
        · simp [right, ha, value]
      · simp [right, hp, he, value]

/-- Extend the two cell tables linearly on canonical bases. -/
def descApp {n k : ℕ} (x y : Cell L) (p : ℕ) :
    Chains n k p →ₗ[ℤ] L.group p :=
  Finsupp.linearCombination ℤ (value x y)

@[simp] theorem descApp_single {n k p : ℕ} (x y : Cell L)
    (b : Basis n k p) (z : ℤ) :
    descApp x y p (Finsupp.single b z) = z • value x y b := by simp [descApp]

/-- On either globe inclusion, the universal map reads that globe's table. -/
theorem descApp_embedApp {n k : ℕ} (hkn : k < n) (x y : Cell L)
    (hxy : x.face true k = y.face false k) (s : Bool) (p : ℕ)
    (u : DirectedGlobeComplex.Chains n p) :
    descApp x y p (embedApp hkn s p u) =
      DirectedGlobeComplex.cellApp n (if s then y else x) p u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z => simp [value_embed hkn x y hxy]

/-- The universal map respects every signed boundary. -/
theorem descApp_differential {n k : ℕ} (hkn : k < n) (x y : Cell L)
    (hxy : x.face true k = y.face false k) (p : ℕ) (u : Chains n k (p+1)) :
    descApp x y p (differential hkn p u) =
      L.differential p (descApp x y (p+1) u) := by
  have hs (s : Bool) (b : DirectedGlobeComplex.Basis n (p+1)) (z : ℤ) :
      descApp x y p (differential hkn p (Finsupp.single (embed hkn s b) z)) =
        L.differential p (descApp x y (p+1) (Finsupp.single (embed hkn s b) z)) := by
    rw [← embedApp_single hkn s b z, ← embedApp_differential,
      descApp_embedApp hkn x y hxy, descApp_embedApp hkn x y hxy]
    exact DirectedGlobeComplex.cellApp_differential n (if s then y else x) p _
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z =>
    rcases left_or_right hkn b with ⟨c, hc⟩ | ⟨c, hc⟩
    · subst b
      exact hs false c z
    · subst b
      exact hs true c z

/-- Both tables have augmentation one on every zero-dimensional basis. -/
theorem descApp_augmentation {n k : ℕ} (x y : Cell L) (u : Chains n k 0) :
    L.augmentation (descApp x y 0 u) = weight n k 0 u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z =>
    simp only [descApp_single, map_zsmul, weight_single, value]
    split_ifs <;> simp [Cell.augmentation]

/-- Positivity of each table entry gives positivity on the full free cone. -/
theorem descApp_positive {n k p : ℕ} (x y : Cell L) (u : Chains n k p)
    (hu : u ∈ positive n k p) : descApp x y p u ∈ L.positive p := by
  classical
  change (u.sum fun b z => z • value x y b) ∈ L.positive p
  apply (L.positive p).sum_mem
  intro b hb
  change u b • value x y b ∈ L.positive p
  rw [← Int.toNat_of_nonneg (hu b), natCast_zsmul]
  apply (L.positive p).nsmul_mem
  unfold value
  split_ifs
  · exact y.positive _ _
  · exact x.positive _ _

/-- The actual positive chain map specified by two matching cell tables. -/
def desc {n k : ℕ} (hkn : k < n) (x y : Cell L)
    (hxy : x.face true k = y.face false k) : Hom (complex n k hkn) L where
  app p := (descApp x y p).toAddMonoidHom
  differential := descApp_differential hkn x y hxy
  augmentation := descApp_augmentation x y
  positive _ _ hu := descApp_positive x y _ hu

/-- Restricting the universal map to either half recovers that half's table. -/
theorem inclusion_desc {n k : ℕ} (hkn : k < n) (x y : Cell L)
    (hxy : x.face true k = y.face false k) (s : Bool) :
    Hom.comp (inclusion hkn s) (desc hkn x y hxy) =
      DirectedGlobeComplex.cellMap n (if s then y else x) := by
  apply Hom.ext_app
  intro p u
  exact descApp_embedApp hkn x y hxy s p u

/-- The two globe inclusions jointly determine every positive chain map. -/
theorem hom_ext {n k : ℕ} (hkn : k < n) {f g : Hom (complex n k hkn) L}
    (hleft : Hom.comp (inclusion hkn false) f = Hom.comp (inclusion hkn false) g)
    (hright : Hom.comp (inclusion hkn true) f = Hom.comp (inclusion hkn true) g) : f = g := by
  apply Hom.ext_app
  intro p u
  have hs (s : Bool) (h : Hom.comp (inclusion hkn s) f = Hom.comp (inclusion hkn s) g)
      (b : DirectedGlobeComplex.Basis n p) (z : ℤ) :
      f.app p (Finsupp.single (embed hkn s b) z) =
        g.app p (Finsupp.single (embed hkn s b) z) := by
    have he := congrArg (fun q : Hom (DirectedGlobeComplex.complex n) L =>
      q.app p (Finsupp.single b z)) h
    change f.app p (embedApp hkn s p (Finsupp.single b z)) =
      g.app p (embedApp hkn s p (Finsupp.single b z)) at he
    simpa only [embedApp_single] using he
  let fp : Chains n k p →+ L.group p := f.app p
  let gp : Chains n k p →+ L.group p := g.app p
  change fp u = gp u
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z =>
    rcases left_or_right hkn b with ⟨c, hc⟩ | ⟨c, hc⟩
    · subst b
      exact hs false hleft c z
    · subst b
      exact hs true hright c z

end

end Thomason.Construction.PastingGlobeBasis

end

section

/-! # A strong order for the signed right-cylinder basis

Endpoint copies have offsets -1 and +1 from three times the original
height; the negative endpoint depends on the parity of the original degree.
Mixed elements have offset zero. Thus the signed tensor differential is
strictly compatible with the order, including its alternating endpoint sign.
-/

namespace Thomason.Construction.RightCylinderBasis

variable {B : ℕ → Type*}

/-- The direct-sum basis of the right tensor with the oriented interval. -/
inductive Basis (B : ℕ → Type*) : ℕ → Type _
  | endpoint {p : ℕ} (a : Bool) (b : B p) : Basis B p
  | mixed {p : ℕ} (b : B p) : Basis B (p+1)

/-- The negative endpoint in the boundary of `b ⊗ [0,1]`. -/
def sourceEndpoint (p : ℕ) : Bool := decide (p % 2 = 1)

/-- Threefold spacing keeps the endpoint offsets inside their original slot. -/
def height (h : ∀ p, B p → ℤ) : {p : ℕ} → Basis B p → ℤ
  | p, .endpoint a b => 3*h p b + if a = sourceEndpoint p then -1 else 1
  | p+1, .mixed b => 3*h p b

/-- Every incidence of the signed tensor differential, indexed by its sign.
`false` denotes negative and `true` denotes positive. -/
inductive Incidence (R : ∀ p, Bool → B p → B (p+1) → Prop) :
    (p : ℕ) → Bool → Basis B p → Basis B (p+1) → Prop
  | endpoint {p : ℕ} {s : Bool} {c : B p} {b : B (p+1)}
      (a : Bool) (hr : R p s c b) :
      Incidence R p s (.endpoint a c) (.endpoint a b)
  | mixed {p : ℕ} {s : Bool} {c : B p} {b : B (p+1)} (hr : R p s c b) :
      Incidence R (p+1) s (.mixed c) (.mixed b)
  | source {p : ℕ} (b : B p) :
      Incidence R p false (.endpoint (sourceEndpoint p) b) (.mixed b)
  | target {p : ℕ} (b : B p) :
      Incidence R p true (.endpoint (!(sourceEndpoint p)) b) (.mixed b)

/-- A base order compatible with negative and positive incidences extends to
all signed incidences of the right-cylinder differential. -/
theorem height_incidence
    (h : ∀ p, B p → ℤ) (R : ∀ p, Bool → B p → B (p+1) → Prop)
    (hR : ∀ p s c b, R p s c b → if s then h (p+1) b < h p c else h p c < h (p+1) b)
    {p : ℕ} {s : Bool} {c : Basis B p} {b : Basis B (p+1)}
    (hi : Incidence R p s c b) :
    if s then height h b < height h c else height h c < height h b := by
  cases hi with
  | endpoint a hr =>
    have hh := hR _ _ _ _ hr
    cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hh ⊢
    all_goals simp only [height]; split_ifs <;> omega
  | mixed hr =>
    have hh := hR _ _ _ _ hr
    cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true, height] at hh ⊢ <;> omega
  | source b => simp [height]
  | target b => simp [height]

/-- The actual two-boundary incidence of the pasted-globe basis. -/
def pastingIncidence {n k : ℕ} (hkn : k < n) (p : ℕ) (a : Bool)
    (c : PastingGlobeBasis.Basis n k p) (b : PastingGlobeBasis.Basis n k (p+1)) : Prop :=
  c = PastingGlobeBasis.face hkn a b

/-- The explicit pasted-globe cylinder has a strong order in every degree. -/
theorem pasting_height_incidence {n k : ℕ} (hkn : k < n)
    {p : ℕ} {s : Bool} {c : Basis (PastingGlobeBasis.Basis n k) p}
    {b : Basis (PastingGlobeBasis.Basis n k) (p+1)}
    (hi : Incidence (pastingIncidence hkn) p s c b) :
    if s then height (fun _ => PastingGlobeBasis.height) b <
        height (fun _ => PastingGlobeBasis.height) c
    else height (fun _ => PastingGlobeBasis.height) c <
        height (fun _ => PastingGlobeBasis.height) b := by
  apply height_incidence _ _ ?_ hi
  intro q a c b hc
  subst c
  cases a
  · exact PastingGlobeBasis.height_source_lt hkn b
  · exact PastingGlobeBasis.height_lt_target hkn b

end Thomason.Construction.RightCylinderBasis

end

section

/-! # Explicit mixed cells of the right chain cylinder

Every positive cell table has a natural prism table. The endpoint in each
positive degree alternates with the degree, exactly as required by the
signed right tensor. This constructs the mixed atoms without assuming
that realization preserves any colimit.
-/

namespace Thomason.Construction.DirectedComplex.RightCylinder

universe u

variable {K L : DirectedComplex.{u}}

/-- The sign of a right mixed boundary is controlled by its degree parity. -/
theorem sign_bodd (p : ℕ) : (-1 : ℤ)^p = if p.bodd then -1 else 1 := by
  rw [neg_one_pow_eq_pow_mod_two, Nat.mod_two_of_bodd]
  cases p.bodd <;> rfl

/-- Which endpoint occurs in the chosen face of the prism. -/
def prismSide (p : ℕ) (a : Bool) : Bool := if a then !p.bodd else p.bodd

/-- A prism has one endpoint chain and the preceding mixed chain in every
positive degree. -/
def prismTable (x : Cell K) (a : Bool) : (p : ℕ) → (rightCylinder K).group p
  | 0 => if a then (0, x.table true 0) else (x.table false 0, 0)
  | p+1 => if prismSide (p+1) a then (0, x.table a (p+1), x.table a p)
      else (x.table a (p+1), 0, x.table a p)

/-- The full prism table satisfies the signed chain equations. -/
theorem prismTable_boundary (x : Cell K) (a : Bool) (p : ℕ) :
    (rightCylinder K).differential p (prismTable x a (p+1)) =
      prismTable x true p - prismTable x false p := by
  cases p with
  | zero =>
    cases a <;> ext <;>
      simp [rightCylinder, differential, prismTable, prismSide, x.boundary]
  | succ p =>
    have hs := sign_bodd (p+1)
    cases hp : p.bodd <;> cases a <;> ext <;>
      simp [rightCylinder, differential, prismTable, prismSide, hp, hs,
        x.boundary]; abel

/-- A natural actual cell of the right cylinder associated to every cell. -/
def prism (x : Cell K) : Cell (rightCylinder K) where
  table := prismTable x
  positive a p := by
    cases p with
    | zero =>
      cases a
      · exact ⟨x.positive false 0, (K.positive 0).zero_mem⟩
      · exact ⟨(K.positive 0).zero_mem, x.positive true 0⟩
    | succ p =>
      change (if prismSide (p+1) a then (0, x.table a (p+1), x.table a p)
        else (x.table a (p+1), 0, x.table a p)) ∈ _
      split_ifs
      · exact ⟨(K.positive _).zero_mem, x.positive a _, x.positive a _⟩
      · exact ⟨x.positive a _, (K.positive _).zero_mem, x.positive a _⟩
  augmentation a := by
    cases a <;> simp [rightCylinder, augmentation, prismTable, x.augmentation]
  boundary := prismTable_boundary x
  finite_support := by
    obtain ⟨N, hN⟩ := x.finite_support
    refine ⟨N+1, ?_⟩
    intro p hp a
    cases p with
    | zero => omega
    | succ p =>
      have hpN : N < p := by omega
      simp [prismTable, hN p hpN a, hN (p+1) (by omega) a]

/-- Prisms increase a finite dimension bound by one. -/
theorem prism_dimension {n : ℕ} (x : Cell K) (hx : K.realization.DimensionLE n x) :
    (rightCylinder K).realization.DimensionLE (n+1) (prism x) := by
  apply Cell.dimensionLE_of_table_zero
  intro p hp a
  cases p with
  | zero => omega
  | succ p =>
    have hn : n < p := by omega
    simp [prism, prismTable, Cell.table_zero_of_dimensionLE hx hn a,
      Cell.table_zero_of_dimensionLE hx (show n < p+1 by omega) a]

/-- A bounded cell contributes its top chain as the literal mixed chain
in the top degree of the prism. -/
theorem prism_top {n : ℕ} (x : Cell K) (hx : K.realization.DimensionLE n x) (a : Bool) :
    (prism x).table a (n+1) = (0, 0, x.table a n) := by
  simp [prism, prismTable, Cell.table_zero_of_dimensionLE hx (Nat.lt_succ_self n) a]

/-- Positive chain maps preserve this explicit prism construction. -/
theorem prism_naturality (f : Hom K L) (x : Cell K) :
    Cell.map (map f) (prism x) = prism (Cell.map f x) := by
  apply Cell.ext
  funext a p
  cases p with
  | zero => cases a <;> simp [prism, prismTable, map, mapMap, Cell.map]
  | succ p =>
    simp only [Cell.map_table, prism, prismTable, map, mapMap]
    split_ifs <;> simp

end Thomason.Construction.DirectedComplex.RightCylinder

end

end OAI
