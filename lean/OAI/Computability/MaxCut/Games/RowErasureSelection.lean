import Mathlib
import OAI.Computability.MaxCut.Encoding.AdviceFibers
import OAI.Computability.MaxCut.Games.AffineWitness

namespace OAI

noncomputable section

/-!
Visible selection of a row-erasure witness. The selected description depends
only on the fixed table function, the row map, and the observed row value.
The full sampled matrix enters only the later event testing its membership in
the already selected slice. Classical choice fixes one witness once and for all;
proof irrelevance makes the choice independent of the goodness proof.
-/

namespace MaxCutGames.Inverse.RowErasure

variable {X Y A S D : Type*}

def SliceFamily.chosenDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) : D :=
  Classical.choose hgood

theorem SliceFamily.chosenDescription_spec (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.rowMap (F.chosenDescription f α a s hgood) = a ∧
      F.rowValue (F.chosenDescription f α a s hgood) = s ∧
      (F.points (F.chosenDescription f α a s hgood)).Nonempty ∧
      α / 2 ≤ F.agreement f (F.chosenDescription f α a s hgood) :=
  Classical.choose_spec hgood

theorem SliceFamily.chosenDescription_congr (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) {a a' : A} {s s' : S}
    (hgood : F.GoodAdvice f α a s) (hgood' : F.GoodAdvice f α a' s')
    (ha : a = a') (hs : s = s') :
    F.chosenDescription f α a s hgood =
      F.chosenDescription f α a' s' hgood' := by
  subst a'
  subst s'
  rfl

/-- A total visible selector. Bad advice has no selected witness. -/
def SliceFamily.selectedDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Option D := by
  classical
  exact if hgood : F.GoodAdvice f α a s then
    some (F.chosenDescription f α a s hgood) else none

theorem SliceFamily.selectedDescription_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.selectedDescription f α a s = some (F.chosenDescription f α a s hgood) := by
  simp only [SliceFamily.selectedDescription, dite_eq_left hgood]

theorem SliceFamily.good_of_selectedDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) {d : D}
    (hselected : F.selectedDescription f α a s = some d) :
    F.GoodAdvice f α a s := by
  classical
  by_contra hgood
  simp only [SliceFamily.selectedDescription, dite_eq_right hgood] at hselected
  cases hselected

theorem SliceFamily.selectedDescription_spec (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) {d : D}
    (hselected : F.selectedDescription f α a s = some d) :
    F.rowMap d = a ∧ F.rowValue d = s ∧ (F.points d).Nonempty ∧
      α / 2 ≤ F.agreement f d := by
  have hgood := F.good_of_selectedDescription f α a s hselected
  rw [F.selectedDescription_of_good f α a s hgood] at hselected
  have hd := Option.some.inj hselected
  rw [← hd]
  exact F.chosenDescription_spec f α a s hgood

theorem SliceFamily.selectedDescription_congr (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) {a a' : A} {s s' : S}
    (ha : a = a') (hs : s = s') :
    F.selectedDescription f α a s = F.selectedDescription f α a' s' := by
  subst a'
  subst s'
  rfl

/-- Good visible advice and the selected column restrictions on the hidden
matrix. The selector receives only its observed row value. -/
def SliceFamily.selectedEvent (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a (F.advice a x) = some d ∧ x ∈ F.points d

def SliceFamily.selectedMatch (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a (F.advice a x) = some d ∧
    x ∈ F.points d ∧ f x = F.target d x

theorem SliceFamily.selectedEvent_iff_of_advice (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) (hx : F.advice a x = s) :
    F.selectedEvent f α a x ↔ x ∈ F.points (F.chosenDescription f α a s hgood) := by
  unfold SliceFamily.selectedEvent
  rw [hx, F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hmem⟩
    have he := Option.some.inj hd
    simpa only [he] using hmem
  · intro hmem
    exact ⟨_, rfl, hmem⟩

theorem SliceFamily.selectedMatch_iff_of_advice (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) (hx : F.advice a x = s) :
    F.selectedMatch f α a x ↔
      x ∈ F.points (F.chosenDescription f α a s hgood) ∧
        f x = F.target (F.chosenDescription f α a s hgood) x := by
  unfold SliceFamily.selectedMatch
  rw [hx, F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hmem, hmatch⟩
    have he := Option.some.inj hd
    simpa only [he] using And.intro hmem hmatch
  · rintro ⟨hmem, hmatch⟩
    exact ⟨_, rfl, hmem, hmatch⟩

theorem SliceFamily.selectedEvent_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X)
    (hx : F.selectedEvent f α a x) : F.goodAt f α a x := by
  obtain ⟨d, hd, _⟩ := hx
  exact F.good_of_selectedDescription f α a (F.advice a x) hd

theorem SliceFamily.selectedMatch_event (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X)
    (hx : F.selectedMatch f α a x) : F.selectedEvent f α a x := by
  obtain ⟨d, hd, hmem, _⟩ := hx
  exact ⟨d, hd, hmem⟩

end MaxCutGames.Inverse.RowErasure

/-!
Finite partition estimates for a selector fixed by visible data. The observation
fibers need not have equal sizes. Each local counting inequality is summed over
the actual fibers, then divided by the size of the hidden sample space.
-/

namespace MaxCutGames.Inverse.RowErasure.SelectionPartition

open scoped BigOperators Classical

variable {X S : Type*} [Fintype X] [Fintype S]

def fiber (observe : X → S) (s : S) : Finset X :=
  Finset.univ.filter fun x => observe x = s

def event (observe : X → S) (good : S → Prop) (chosen : S → Finset X)
    (x : X) : Prop :=
  good (observe x) ∧ x ∈ chosen (observe x)

def matchEvent (observe : X → S) (good : S → Prop) (chosen : S → Finset X)
    (hit : S → X → Prop) (x : X) : Prop :=
  event observe good chosen x ∧ hit (observe x) x

/-- Arbitrary real summands can be compared fiber by fiber. No uniformity of
the induced observation distribution is asserted or required. -/
theorem expect_le_expect_of_fiber_sum_le (observe : X → S) (f g : X → ℝ)
    (hle : ∀ s, (∑ x ∈ fiber observe s, f x) ≤ ∑ x ∈ fiber observe s, g x) :
    Finset.univ.expect f ≤ Finset.univ.expect g := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.sum_fiberwise Finset.univ observe f,
    ← Finset.sum_fiberwise Finset.univ observe g]
  exact Finset.sum_le_sum fun s _ => hle s

omit [Fintype S] in
/-- On good visible data, the selected event sums exactly over the selected
points, including for arbitrary real weights on the hidden sample. -/
theorem sum_event_mul_fiber (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (s : S) (hgood : good s) (w : X → ℝ) :
    (∑ x ∈ fiber observe s, indicator (event observe good chosen x) * w x) =
      ∑ x ∈ chosen s, w x := by
  have hsub : chosen s ⊆ fiber observe s := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, support s x hx⟩
  calc
    _ = ∑ x ∈ fiber observe s, if x ∈ chosen s then w x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      simp [event, indicator, hobs, hgood, ite_mul]
    _ = ∑ x ∈ chosen s, if x ∈ chosen s then w x else 0 := by
      exact (Finset.sum_subset hsub (fun _ _ hnot => ite_eq_right hnot)).symm
    _ = ∑ x ∈ chosen s, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact ite_eq_left hx

omit [Fintype S] in
theorem sum_event_fiber (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (s : S) (hgood : good s) :
    (∑ x ∈ fiber observe s, indicator (event observe good chosen x)) =
      ((chosen s).card : ℝ) := by
  simpa using sum_event_mul_fiber observe good chosen support s hgood (fun _ => 1)

omit [Fintype S] in
theorem sum_match_fiber (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (hit : S → X → Prop) (s : S) (hgood : good s) :
    (∑ x ∈ fiber observe s, indicator (matchEvent observe good chosen hit x)) =
      ∑ x ∈ chosen s, indicator (hit s x) := by
  calc
    _ = ∑ x ∈ fiber observe s,
        indicator (event observe good chosen x) * indicator (hit s x) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      by_cases hevent : event observe good chosen x <;>
        by_cases hhit : hit s x <;>
        simp [matchEvent, indicator, hevent, hobs, hhit]
    _ = ∑ x ∈ chosen s, indicator (hit s x) :=
      sum_event_mul_fiber observe good chosen support s hgood (fun x => indicator (hit s x))

/-- A lower fraction inside every good fiber gives the same lower fraction
of the actual good-advice mass. Empty fibers and empty sample spaces are valid. -/
theorem mass_event_ge (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (c : ℝ)
    (hsize : ∀ s, good s →
      c * ((fiber observe s).card : ℝ) ≤ ((chosen s).card : ℝ)) :
    c * uniformMass (fun x => good (observe x)) ≤
      uniformMass (event observe good chosen) := by
  unfold uniformMass
  rw [Finset.mul_expect]
  apply expect_le_expect_of_fiber_sum_le observe
  intro s
  by_cases hgood : good s
  · rw [sum_event_fiber observe good chosen support s hgood]
    calc
      (∑ x ∈ fiber observe s, c * indicator (good (observe x))) =
          c * ((fiber observe s).card : ℝ) := by
        calc
          _ = ∑ _x ∈ fiber observe s, c := by
            apply Finset.sum_congr rfl
            intro x hx
            have hobs : observe x = s := (Finset.mem_filter.mp hx).2
            simp [indicator, hobs, hgood]
          _ = _ := by simp [mul_comm]
      _ ≤ _ := hsize s hgood
  · have hz : ∀ x ∈ fiber observe s,
        indicator (good (observe x)) = 0 ∧
          indicator (event observe good chosen x) = 0 := by
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      simp [indicator, event, hobs, hgood]
    have hleft : (∑ x ∈ fiber observe s, c * indicator (good (observe x))) = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [(hz x hx).1, mul_zero]
    have hright : (∑ x ∈ fiber observe s, indicator (event observe good chosen x)) = 0 :=
      Finset.sum_eq_zero fun x hx => (hz x hx).2
    rw [hleft, hright]

/-- A matching fraction in every selected good fiber survives averaging over
the hidden sample space, without any equiprobability assumption on fibers. -/
theorem mass_match_ge (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (hit : S → X → Prop) (β : ℝ)
    (hmatch : ∀ s, good s →
      β * ((chosen s).card : ℝ) ≤ ∑ x ∈ chosen s, indicator (hit s x)) :
    β * uniformMass (event observe good chosen) ≤
      uniformMass (matchEvent observe good chosen hit) := by
  unfold uniformMass
  rw [Finset.mul_expect]
  apply expect_le_expect_of_fiber_sum_le observe
  intro s
  by_cases hgood : good s
  · rw [← Finset.mul_sum, sum_event_fiber observe good chosen support s hgood,
      sum_match_fiber observe good chosen support hit s hgood]
    exact hmatch s hgood
  · have hz : ∀ x ∈ fiber observe s,
        indicator (event observe good chosen x) = 0 ∧
          indicator (matchEvent observe good chosen hit x) = 0 := by
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      simp [indicator, event, matchEvent, hobs, hgood]
    have hleft : (∑ x ∈ fiber observe s, β * indicator (event observe good chosen x)) = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [(hz x hx).1, mul_zero]
    have hright :
        (∑ x ∈ fiber observe s, indicator (matchEvent observe good chosen hit x)) = 0 :=
      Finset.sum_eq_zero fun x hx => (hz x hx).2
    rw [hleft, hright]

end MaxCutGames.Inverse.RowErasure.SelectionPartition

/-!
Exact mass of a nonempty column slice within a fixed row-advice fiber. A
column span of dimension at most `r` costs at most `ell*r` binary degrees of
freedom. All inhomogeneous values are represented by the chosen base point.
-/

namespace MaxCutGames.Inverse.RowErasureColumnMass

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Decoder.AdviceFibers
open MaxCutGames.Inverse.RowErasureSliceQuotient

variable {E K R : Type*}
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K]
  [AddCommGroup R] [Module F2 R]

theorem card_affineSlice (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    Nat.card (AffineSlice A Q M₀) =
      2 ^ (Module.finrank F2 (E ⧸ Q) * Module.finrank F2 A.ker) := by
  rw [Nat.card_congr (equiv A Q M₀).symm,
    Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

theorem card_rowFiber (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K) :
    Nat.card (RowFiber A (A.comp M₀)) =
      2 ^ (Module.finrank F2 E * Module.finrank F2 A.ker) := by
  rw [Nat.card_congr (rowFiberEquiv A (A.comp M₀) M₀ rfl).symm,
    Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

/-- The exact number of row-fiber points for each compatible specification on
the column span. Dependent column equations cost only their actual rank. -/
theorem card_rowFiber_eq_mul (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    Nat.card (RowFiber A (A.comp M₀)) = Nat.card (AffineSlice A Q M₀) *
      2 ^ (Module.finrank F2 Q * Module.finrank F2 A.ker) := by
  rw [card_rowFiber, card_affineSlice, ← pow_add, ← Nat.add_mul,
    Q.finrank_quotient_add_finrank]

/-- A denominator-free bound by the listed column count and ambient output
dimension, with no independence or full-rank hypothesis. -/
theorem card_rowFiber_le_mul (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) (ell r : ℕ)
    (hQ : Module.finrank F2 Q ≤ r) (hK : Module.finrank F2 K ≤ ell) :
    Nat.card (RowFiber A (A.comp M₀)) ≤
      Nat.card (AffineSlice A Q M₀) * 2 ^ (ell * r) := by
  have hker : Module.finrank F2 A.ker ≤ ell := A.ker.finrank_le.trans hK
  have hexponent : Module.finrank F2 Q * Module.finrank F2 A.ker ≤ ell * r := by
    simpa only [Nat.mul_comm r ell] using Nat.mul_le_mul hQ hker
  rw [card_rowFiber_eq_mul A Q M₀]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexponent)

/-- The exact uniform fraction of the row fiber occupied by its compatible
affine column slice. -/
theorem column_fraction_eq (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    (Nat.card (AffineSlice A Q M₀) : ℝ) /
        (Nat.card (RowFiber A (A.comp M₀)) : ℝ) =
      1 / (2 : ℝ) ^ (Module.finrank F2 Q * Module.finrank F2 A.ker) := by
  have hs : (0 : ℝ) < Nat.card (AffineSlice A Q M₀) := by
    rw [card_affineSlice]
    positivity
  rw [card_rowFiber_eq_mul A Q M₀]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_mul_cancel_left₀ hs.ne', one_div]

/-- At most `r` independent column constraints retain at least the fraction
`2^(-ell*r)` of any nonempty row-advice fiber. -/
theorem column_fraction_ge (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) (ell r : ℕ)
    (hQ : Module.finrank F2 Q ≤ r) (hK : Module.finrank F2 K ≤ ell) :
    1 / (2 : ℝ) ^ (ell * r) ≤
      (Nat.card (AffineSlice A Q M₀) : ℝ) /
        (Nat.card (RowFiber A (A.comp M₀)) : ℝ) := by
  rw [column_fraction_eq]
  have hker : Module.finrank F2 A.ker ≤ ell := A.ker.finrank_le.trans hK
  have hexponent : Module.finrank F2 Q * Module.finrank F2 A.ker ≤ ell * r := by
    simpa only [Nat.mul_comm r ell] using Nat.mul_le_mul hQ hker
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent)

end MaxCutGames.Inverse.RowErasureColumnMass

/-!
Exact uniform parametrization of the concrete row/column slice.  The quotient
parameter describes every point, not only a lower-bounding subfamily.  Affine
targets retain the base-point contribution and their original intercept.
-/

namespace MaxCutGames.Inverse.Shortcode.Slice

open scoped BigOperators Matrix

variable {ell m : ℕ}

theorem difference_row_zero (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    S.rowMap.comp (Matrix.toLin' (M - M₀)) = 0 := by
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  have hrow : LinearMap.toMatrix' S.rowMap = S.rowCoefficient :=
    LinearMap.toMatrix'_toLin' S.rowCoefficient
  rw [hrow]
  ext i j
  change (∑ a, S.rowCoefficient i a * (M - M₀) a j) = 0
  simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hM.1 i j, h₀.1 i j, sub_self]

theorem difference_range_le (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    LinearMap.range (Matrix.toLin' (M - M₀)) ≤ S.rowMap.ker := by
  rintro _ ⟨v, rfl⟩
  have h := LinearMap.congr_fun (S.difference_row_zero hM h₀) v
  exact h

theorem difference_vanishes_columns (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    S.columnSpan ≤ LinearMap.ker (Matrix.toLin' (M - M₀)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change Matrix.toLin' (M - M₀) (S.columnCoefficient i) = 0
  have he : Matrix.toLin' (M - M₀) (S.columnCoefficient i) =
      evaluate M (S.columnCoefficient i) - evaluate M₀ (S.columnCoefficient i) := by
    rw [map_sub, LinearMap.sub_apply]
    rfl
  rw [he, hM.2 i, h₀.2 i, sub_self]

/-- Every actual slice point differs from the base by a unique quotient map. -/
theorem directionEmbedding_surjective (S : Slice ell m)
    (M₀ : Mat ell m) (h₀ : S.Contains M₀) :
    Function.Surjective (S.directionEmbedding M₀ h₀) := by
  intro M
  have hM : S.Contains M.val := by
    simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using M.property
  obtain ⟨N, hN⟩ :=
    RowErasureSliceQuotient.exists_direction_of_row_and_column
      S.rowMap S.columnSpan (Matrix.toLin' (M.val - M₀))
      (S.difference_vanishes_columns hM h₀) (S.difference_range_le hM h₀)
  have hdir : S.directionMap N = Matrix.toLin' (M.val - M₀) := hN
  have hmat : S.directionMatrix N = M.val - M₀ := by
    unfold directionMatrix
    rw [hdir, LinearMap.toMatrix'_toLin']
  refine ⟨N, ?_⟩
  apply Subtype.ext
  change M₀ + S.directionMatrix N = M.val
  rw [hmat]
  abel

/-- The concrete simultaneous slice is exactly an affine copy of
`Hom(domain / columnSpan, commonRowKernel)`. -/
def directionEquiv (S : Slice ell m) (M₀ : Mat ell m) (h₀ : S.Contains M₀) :
    S.Directions ≃ S.points :=
  Equiv.ofBijective (S.directionEmbedding M₀ h₀)
    ⟨(S.directionEmbedding M₀ h₀).injective, S.directionEmbedding_surjective M₀ h₀⟩

@[simp] theorem directionEquiv_val (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) (N : S.Directions) :
    (S.directionEquiv M₀ h₀ N).val = M₀ + S.directionMatrix N := rfl

instance directionsFintype (S : Slice ell m) : Fintype S.Directions := by
  classical
  letI : Fintype (Vector m ⧸ S.columnSpan) := Fintype.ofFinite _
  letI : Fintype S.rowMap.ker := Fintype.ofFinite _
  exact Fintype.ofInjective
    (fun N : S.Directions => (N : (Vector m ⧸ S.columnSpan) → S.rowMap.ker))
    DFunLike.coe_injective

theorem card_points_eq_directions (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) : S.points.card = Nat.card S.Directions := by
  rw [← Nat.card_eq_finsetCard, Nat.card_congr (S.directionEquiv M₀ h₀).symm]

/-- Uniform quotient parameters give precisely the uniform measure on the
actual finite slice, including all its inhomogeneous row/column equations. -/
theorem points_expect_eq_directions (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) (f : Mat ell m → ℝ) :
    S.points.expect f = 𝔼 N : S.Directions, f (M₀ + S.directionMatrix N) := by
  have h := Fintype.expect_equiv (S.directionEquiv M₀ h₀)
    (fun N => f (M₀ + S.directionMatrix N)) (fun M => f M.val) (fun _ => rfl)
  rw [h, Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  simp only [Fintype.card_coe, Finset.sum_coe_sort]

theorem directionMatrix_evaluate (S : Slice ell m) (N : S.Directions) (z : Vector m) :
    evaluate (S.directionMatrix N) z = (N (S.columnSpan.mkQ z) : Vector ell) := by
  change (S.directionMatrix N) *ᵥ z = _
  rw [directionMatrix, LinearMap.toMatrix'_mulVec]
  rfl

/-- The decoder's affine offset is the original intercept plus the base
matrix evaluated at the target; it is not silently replaced by zero. -/
theorem direction_affine_target (S : Slice ell m) (M₀ : Mat ell m)
    (N : S.Directions) (z : Vector m) (u : Vector ell) :
    evaluate (M₀ + S.directionMatrix N) z + u =
      (N (S.columnSpan.mkQ z) : Vector ell) + (evaluate M₀ z + u) := by
  have he : evaluate (M₀ + S.directionMatrix N) z =
      evaluate M₀ z + evaluate (S.directionMatrix N) z := by
    ext i
    simp [evaluate, add_mul, Finset.sum_add_distrib]
  rw [he, S.directionMatrix_evaluate]
  abel

theorem affineAgreement_eq_directions (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) (f : Mat ell m → Vector ell)
    (z : Vector m) (u : Vector ell) :
    S.affineAgreement f z u = 𝔼 N : S.Directions,
      if f (M₀ + S.directionMatrix N) =
        (N (S.columnSpan.mkQ z) : Vector ell) + (evaluate M₀ z + u)
      then (1 : ℝ) else 0 := by
  classical
  rw [affineAgreement, S.points_expect_eq_directions M₀ h₀]
  simp only [S.direction_affine_target]

end MaxCutGames.Inverse.Shortcode.Slice

/-!
The actual finite matrix column event occupies at least `2^(-ell*r)` of its
row-advice fiber. This connects the intrinsic quotient-map count to the padded
descriptions used by the selector, without assuming independent equations.
-/

namespace MaxCutGames.Inverse.RowErasureDescriptionColumnMass

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasureDescriptions
open MaxCutGames.Inverse.RowErasureMatrix
open scoped BigOperators Classical

def rowFiber {ell m r : ℕ} (A : RowMap ell r) (s : Mat r m) :
    Finset (Mat ell m) :=
  Finset.univ.filter fun M => rowAdvice A M = s

@[simp] theorem mem_rowFiber {ell m r : ℕ} (A : RowMap ell r) (s : Mat r m)
    (M : Mat ell m) : M ∈ rowFiber A s ↔ rowAdvice A M = s := by
  simp [rowFiber]

/-- Forget only the column equations of a slice. -/
def rowOnly {ell m : ℕ} (S : Slice ell m) : Slice ell m where
  rows := S.rows
  columns := 0
  rowCoefficient := S.rowCoefficient
  rowValue := S.rowValue
  columnCoefficient := Fin.elim0
  columnValue := Fin.elim0

theorem rowOnly_contains_iff {ell m : ℕ} (S : Slice ell m) (M : Mat ell m) :
    (rowOnly S).Contains M ↔ rowAdvice S.rowCoefficient M = S.rowValue := by
  constructor
  · intro h
    funext i j
    exact h.1 i j
  · intro h
    constructor
    · intro i j
      exact congrFun (congrFun h i) j
    · intro i
      exact Fin.elim0 i

theorem rowOnly_points {ell m : ℕ} (S : Slice ell m) :
    (rowOnly S).points = rowFiber S.rowCoefficient S.rowValue := by
  ext M
  simp only [Slice.points, rowFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    rowOnly_contains_iff]

theorem contains_rowOnly {ell m : ℕ} (S : Slice ell m) {M : Mat ell m}
    (hM : S.Contains M) : (rowOnly S).Contains M := by
  exact ⟨hM.1, fun i => Fin.elim0 i⟩

theorem rowOnly_columnSpan {ell m : ℕ} (S : Slice ell m) :
    (rowOnly S).columnSpan = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro _ ⟨i, _⟩
  exact Fin.elim0 i

theorem rowOnly_quotient_finrank {ell m : ℕ} (S : Slice ell m) :
    Module.finrank F2 (Shortcode.Vector m ⧸ (rowOnly S).columnSpan) = m := by
  have h := (rowOnly S).columnSpan.finrank_quotient_add_finrank
  have hz : Module.finrank F2 (rowOnly S).columnSpan = 0 := by
    rw [rowOnly_columnSpan]
    simp
  have hm : Module.finrank F2 (Shortcode.Vector m) = m := by simp [Shortcode.Vector]
  rw [hz, add_zero, hm] at h
  exact h

/-- The size of an actual nonempty row fiber, in the same coordinates used by
the selector's uniform matrix sample. -/
theorem rowFiber_card {ell m : ℕ} (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) :
    (rowFiber S.rowCoefficient S.rowValue).card =
      2 ^ (m * Module.finrank F2 S.rowMap.ker) := by
  rw [← rowOnly_points S,
    (rowOnly S).card_points_eq_directions M₀ (contains_rowOnly S h₀),
    (rowOnly S).card_directions, rowOnly_quotient_finrank]
  rfl

theorem rowFiber_nonempty {ell m r : ℕ} (d : Description ell m r)
    (hne : d.toSlice.points.Nonempty) : (rowFiber d.1 d.2.1).Nonempty := by
  obtain ⟨M, hM⟩ := hne
  have hc : d.toSlice.Contains M := (Finset.mem_filter.mp hM).2
  refine ⟨M, (mem_rowFiber _ _ _).mpr ?_⟩
  funext i j
  exact hc.1 i j

/-- The chosen nonempty column event has the required mass inside its actual
row-advice fiber. The target coefficient and intercept do not affect its size. -/
theorem column_fraction_ge {ell m r : ℕ} (d : Description ell m r)
    (hne : d.toSlice.points.Nonempty) :
    1 / (2 : ℝ) ^ (ell * r) ≤
      (d.toSlice.points.card : ℝ) / ((rowFiber d.1 d.2.1).card : ℝ) := by
  obtain ⟨M₀, hM₀⟩ := hne
  have h₀ : d.toSlice.Contains M₀ := (Finset.mem_filter.mp hM₀).2
  have hs : d.toSlice.points.card = Nat.card
      (RowErasureSliceQuotient.AffineSlice d.toSlice.rowMap d.toSlice.columnSpan
        (Matrix.toLin' M₀)) := by
    rw [d.toSlice.card_points_eq_directions M₀ h₀, d.toSlice.card_directions,
      RowErasureColumnMass.card_affineSlice]
  have hr : (rowFiber d.1 d.2.1).card = Nat.card
      (MaxCutGames.Decoder.AdviceFibers.RowFiber d.toSlice.rowMap
        (d.toSlice.rowMap.comp (Matrix.toLin' M₀))) := by
    have hm : Module.finrank F2 (Shortcode.Vector m) = m := by simp [Shortcode.Vector]
    rw [RowErasureColumnMass.card_rowFiber, hm]
    exact rowFiber_card d.toSlice M₀ h₀
  have h := RowErasureColumnMass.column_fraction_ge
    d.toSlice.rowMap d.toSlice.columnSpan (Matrix.toLin' M₀) ell r
    d.toSlice.columnSpan_finrank_le (by simp [Shortcode.Vector])
  rwa [← hs, ← hr] at h

end MaxCutGames.Inverse.RowErasureDescriptionColumnMass

/-!
The selected column event under the actual uniform matrix and row-map samples.
The witness is fixed by visible row advice before testing the hidden matrix.
Fiber sizes are retained explicitly; no uniformity of row values is assumed.
The final averaging lemmas also allow arbitrary nonnegative context weights.
-/

namespace MaxCutGames.Inverse.RowErasure

open scoped BigOperators

variable {X Y A S D : Type*}

def SliceFamily.selectedPoints (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Finset X :=
  match F.selectedDescription f α a s with
  | none => ∅
  | some d => F.points d

def SliceFamily.selectedHit (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a s = some d ∧ f x = F.target d x

theorem SliceFamily.selectedPoints_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.selectedPoints f α a s = F.points (F.chosenDescription f α a s hgood) := by
  unfold SliceFamily.selectedPoints
  rw [F.selectedDescription_of_good f α a s hgood]

theorem SliceFamily.selectedHit_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) :
    F.selectedHit f α a s x ↔ f x = F.target (F.chosenDescription f α a s hgood) x := by
  unfold SliceFamily.selectedHit
  rw [F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hhit⟩
    have he := Option.some.inj hd
    simpa only [he] using hhit
  · intro hhit
    exact ⟨_, rfl, hhit⟩

theorem SliceFamily.selectedPoints_support (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) (x : X)
    (hx : x ∈ F.selectedPoints f α a s) : F.advice a x = s := by
  classical
  cases hd : F.selectedDescription f α a s with
  | none => simp [SliceFamily.selectedPoints, hd] at hx
  | some d =>
    have hspec := F.selectedDescription_spec f α a s hd
    have hmem : x ∈ F.points d := by
      simpa only [SliceFamily.selectedPoints, hd] using hx
    have h := F.points_row d x hmem
    rw [hspec.1, hspec.2.1] at h
    exact h

theorem SliceFamily.selectedEvent_iff_points (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) :
    F.selectedEvent f α a x ↔
      F.GoodAdvice f α a (F.advice a x) ∧
        x ∈ F.selectedPoints f α a (F.advice a x) := by
  classical
  by_cases hg : F.GoodAdvice f α a (F.advice a x)
  · rw [F.selectedEvent_iff_of_advice f α a (F.advice a x) hg x rfl,
      F.selectedPoints_of_good f α a (F.advice a x) hg]
    simp only [hg, true_and]
  · constructor
    · intro hx
      exact (hg (F.selectedEvent_good f α a x hx)).elim
    · intro hx
      exact (hg hx.1).elim

theorem SliceFamily.selectedMatch_iff_points (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) :
    F.selectedMatch f α a x ↔
      (F.GoodAdvice f α a (F.advice a x) ∧
        x ∈ F.selectedPoints f α a (F.advice a x)) ∧
          F.selectedHit f α a (F.advice a x) x := by
  classical
  by_cases hg : F.GoodAdvice f α a (F.advice a x)
  · rw [F.selectedMatch_iff_of_advice f α a (F.advice a x) hg x rfl,
      F.selectedPoints_of_good f α a (F.advice a x) hg,
      F.selectedHit_of_good f α a (F.advice a x) hg x]
    simp only [hg, true_and]
  · constructor
    · intro hx
      exact (hg (F.selectedEvent_good f α a x (F.selectedMatch_event f α a x hx))).elim
    · intro hx
      exact (hg hx.1.1).elim

theorem SliceFamily.selectedPoints_match_sum (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    (α / 2) * ((F.selectedPoints f α a s).card : ℝ) ≤
      ∑ x ∈ F.selectedPoints f α a s, indicator (F.selectedHit f α a s x) := by
  classical
  have hspec := F.chosenDescription_spec f α a s hgood
  have hcard : (0 : ℝ) < (F.points (F.chosenDescription f α a s hgood)).card :=
    Nat.cast_pos.mpr hspec.2.2.1.card_pos
  have hagree := hspec.2.2.2
  rw [SliceFamily.agreement, Finset.expect_eq_sum_div_card] at hagree
  rw [F.selectedPoints_of_good f α a s hgood]
  simp_rw [F.selectedHit_of_good f α a s hgood]
  exact (le_div_iff₀ hcard).mp hagree

end MaxCutGames.Inverse.RowErasure

namespace MaxCutGames.Inverse.RowErasureMatrix

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasure
open MaxCutGames.Inverse.RowErasureDescriptions
open MaxCutGames.Inverse.RowErasureDescriptionColumnMass
open scoped BigOperators

variable {ell m r : ℕ}

theorem selectedPoints_column_mass (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) (s : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A s) :
    (1 / (2 : ℝ) ^ (ell * r)) * ((rowFiber A s).card : ℝ) ≤
      (((family ell m r).selectedPoints f α A s).card : ℝ) := by
  let d := (family ell m r).chosenDescription f α A s hgood
  have hspec := (family ell m r).chosenDescription_spec f α A s hgood
  have hne : d.toSlice.points.Nonempty := hspec.2.2.1
  have hcard : (0 : ℝ) < (rowFiber d.1 d.2.1).card :=
    Nat.cast_pos.mpr (rowFiber_nonempty d hne).card_pos
  have h := (le_div_iff₀ hcard).mp (column_fraction_ge d hne)
  have hA : d.1 = A := hspec.1
  have hs : d.2.1 = s := hspec.2.1
  rw [hA, hs] at h
  rw [(family ell m r).selectedPoints_of_good f α A s hgood]
  exact h

theorem selected_event_mass_ge (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) :
    (1 / (2 : ℝ) ^ (ell * r)) *
      uniformMass ((family ell m r).goodAt f α A) ≤
        uniformMass ((family ell m r).selectedEvent f α A) := by
  have h := SelectionPartition.mass_event_ge
    ((family ell m r).advice A) ((family ell m r).GoodAdvice f α A)
    ((family ell m r).selectedPoints f α A)
    ((family ell m r).selectedPoints_support f α A)
    (1 / (2 : ℝ) ^ (ell * r))
    (fun s hg => by
      have hfiber : SelectionPartition.fiber ((family ell m r).advice A) s =
          rowFiber A s := by
        ext M
        simp only [SelectionPartition.fiber, rowFiber, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rfl
      rw [hfiber]
      exact selectedPoints_column_mass f α A s hg)
  have he : SelectionPartition.event ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A) =
      (family ell m r).selectedEvent f α A := by
    funext M
    exact propext ((family ell m r).selectedEvent_iff_points f α A M).symm
  rw [he] at h
  exact h

theorem selected_match_mass_ge (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) :
    (α / 2) * uniformMass ((family ell m r).selectedEvent f α A) ≤
      uniformMass ((family ell m r).selectedMatch f α A) := by
  have h := SelectionPartition.mass_match_ge
    ((family ell m r).advice A) ((family ell m r).GoodAdvice f α A)
    ((family ell m r).selectedPoints f α A)
    ((family ell m r).selectedPoints_support f α A)
    ((family ell m r).selectedHit f α A)
    (α / 2) ((family ell m r).selectedPoints_match_sum f α A)
  have he : SelectionPartition.event ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A) =
      (family ell m r).selectedEvent f α A := by
    funext M
    exact propext ((family ell m r).selectedEvent_iff_points f α A M).symm
  have hm : SelectionPartition.matchEvent ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A)
      ((family ell m r).selectedHit f α A) =
      (family ell m r).selectedMatch f α A := by
    funext M
    exact propext ((family ell m r).selectedMatch_iff_points f α A M).symm
  rw [he, hm] at h
  exact h

def selectedEventMass (r : ℕ) (f : Mat ell m → Vector ell) (α : ℝ) : ℝ :=
  𝔼 A : RowMap ell r, uniformMass ((family ell m r).selectedEvent f α A)

def selectedMatchMass (r : ℕ) (f : Mat ell m → Vector ell) (α : ℝ) : ℝ :=
  𝔼 A : RowMap ell r, uniformMass ((family ell m r).selectedMatch f α A)

theorem selectedEventMass_ge (f : Mat ell m → Vector ell) (α : ℝ) :
    (1 / (2 : ℝ) ^ (ell * r)) * adviceMass ((family ell m r).goodAt f α) ≤
      selectedEventMass r f α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun (A : RowMap ell r) _ => selected_event_mass_ge f α A)
  rw [← Finset.mul_expect] at h
  have hadvice : (𝔼 A : RowMap ell r, uniformMass ((family ell m r).goodAt f α A)) =
      adviceMass ((family ell m r).goodAt f α) := by
    simp only [uniformMass, adviceMass]
    exact Finset.expect_comm _ _ _
  rw [hadvice] at h
  exact h

theorem selectedMatchMass_ge (f : Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * selectedEventMass r f α ≤ selectedMatchMass r f α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun (A : RowMap ell r) _ => selected_match_mass_ge f α A)
  rw [← Finset.mul_expect] at h
  exact h

/-- Context weights may be the pushforward of verifier seeds and need not be
uniform on distinct questions. Normalization is not needed for this inequality. -/
theorem selectedEventMass_weighted_ge {Q : Type*} [Fintype Q]
    (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) (f : Q → Mat ell m → Vector ell)
    (α g₀ : ℝ)
    (hgood : g₀ ≤ ∑ q, w q * adviceMass ((family ell m r).goodAt (f q) α)) :
    (1 / (2 : ℝ) ^ (ell * r)) * g₀ ≤ ∑ q, w q * selectedEventMass r (f q) α := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun q _ =>
    mul_le_mul_of_nonneg_left (selectedEventMass_ge (r := r) (f q) α) (hw q))
  have heq : (∑ q, w q * ((1 / (2 : ℝ) ^ (ell * r)) *
      adviceMass ((family ell m r).goodAt (f q) α))) =
      (1 / (2 : ℝ) ^ (ell * r)) *
        ∑ q, w q * adviceMass ((family ell m r).goodAt (f q) α) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [heq] at h
  exact (mul_le_mul_of_nonneg_left hgood (by positivity)).trans h

theorem selectedMatchMass_weighted_ge {Q : Type*} [Fintype Q]
    (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) (f : Q → Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * (∑ q, w q * selectedEventMass r (f q) α) ≤
      ∑ q, w q * selectedMatchMass r (f q) α := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun q _ =>
    mul_le_mul_of_nonneg_left (selectedMatchMass_ge (r := r) (f q) α) (hw q))
  have heq : (∑ q, w q * ((α / 2) * selectedEventMass r (f q) α)) =
      (α / 2) * (∑ q, w q * selectedEventMass r (f q) α) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rwa [heq] at h

theorem selectedMatchMass_conditional_ge {Q : Type*} [Fintype Q]
    (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) (f : Q → Mat ell m → Vector ell) (α : ℝ)
    (hpositive : 0 < ∑ q, w q * selectedEventMass r (f q) α) :
    α / 2 ≤ (∑ q, w q * selectedMatchMass r (f q) α) /
      (∑ q, w q * selectedEventMass r (f q) α) :=
  (le_div_iff₀ hpositive).mpr (selectedMatchMass_weighted_ge w hw f α)

/-- The same bound for a uniform finite seed space, allowing repeated contexts. -/
theorem selectedEventMass_contextual_ge {Q : Type*} [Fintype Q]
    (f : Q → Mat ell m → Vector ell) (α g₀ : ℝ)
    (hgood : g₀ ≤ 𝔼 q, adviceMass ((family ell m r).goodAt (f q) α)) :
    (1 / (2 : ℝ) ^ (ell * r)) * g₀ ≤ 𝔼 q, selectedEventMass r (f q) α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun q _ => selectedEventMass_ge (r := r) (f q) α)
  rw [← Finset.mul_expect] at h
  exact (mul_le_mul_of_nonneg_left hgood (by positivity)).trans h

theorem selectedMatchMass_contextual_ge {Q : Type*} [Fintype Q]
    (f : Q → Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * (𝔼 q, selectedEventMass r (f q) α) ≤
      𝔼 q, selectedMatchMass r (f q) α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun q _ => selectedMatchMass_ge (r := r) (f q) α)
  rwa [← Finset.mul_expect] at h

end MaxCutGames.Inverse.RowErasureMatrix

end

end OAI
