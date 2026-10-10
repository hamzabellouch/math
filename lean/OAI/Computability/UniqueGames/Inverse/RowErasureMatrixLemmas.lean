import OAI.Computability.UniqueGames.Inverse.RowErasureLemmas
import OAI.Computability.UniqueGames.Inverse.RowErasureTail
import OAI.Computability.UniqueGames.Inverse.ShortcodeInterfaceLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open scoped BigOperators Classical

noncomputable section

def rowAdvice {ell m r : ℕ} (A : RowMap ell r) (M : Mat ell m) : Mat r m :=
  fun i j => ∑ a, A i a * M a j

def family (ell m r : ℕ) :
    SliceFamily (Mat ell m) (Vector ell) (RowMap ell r) (Mat r m)
      (Description ell m r) where
  advice := rowAdvice
  rowMap := fun d => d.1
  rowValue := fun d => d.2.1
  points := fun d => d.toSlice.points
  target := fun d M => evaluate M d.coefficient + d.intercept
  points_row := by
    intro d M hM
    have h : d.toSlice.Contains M := (Finset.mem_filter.mp hM).2
    funext i j
    exact h.1 i j

theorem family_agreement {ell m r : ℕ} (d : Description ell m r)
    (f : Mat ell m → Vector ell) :
    (family ell m r).agreement f d =
      d.toSlice.affineAgreement f d.coefficient d.intercept := by
  unfold SliceFamily.agreement Slice.affineAgreement
  apply Finset.expect_congr rfl
  intro M _
  change indicator (f M = evaluate M d.coefficient + d.intercept) = _
  by_cases h : f M = evaluate M d.coefficient + d.intercept
  · simp [indicator, h]
  · simp [indicator, h]

abbrev Samples (ell m : ℕ) := Mat ell m × Vector ell × Vector m

def left {ell m : ℕ} (e : Samples ell m) : Mat ell m := e.1

def right {ell m : ℕ} (e : Samples ell m) : Mat ell m :=
  e.1 + rankOne e.2.1 e.2.2

theorem expect_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X × Y → ℝ) :
    Finset.univ.expect f =
      Finset.univ.expect (fun x => Finset.univ.expect fun y => f (x, y)) := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, mul_inv_rev]
  ring

theorem left_uniform {ell m : ℕ} (B : Mat ell m → Prop) :
    uniformMass (fun e : Samples ell m => B (left e)) = uniformMass B := by
  unfold uniformMass
  rw [expect_prod]
  simp only [left, Fintype.expect_const]

/-- Translation of the sampled matrix is a permutation while the two sampled
factors remain fixed; this also covers either factor being zero. -/
def stepEquiv (ell m : ℕ) : Samples ell m ≃ Samples ell m where
  toFun e := (right e, e.2)
  invFun e := (e.1 - rankOne e.2.1 e.2.2, e.2)
  left_inv e := by
    apply Prod.ext
    · exact add_sub_cancel_right e.1 (rankOne e.2.1 e.2.2)
    · rfl
  right_inv e := by
    apply Prod.ext
    · exact sub_add_cancel e.1 (rankOne e.2.1 e.2.2)
    · rfl

theorem right_uniform {ell m : ℕ} (B : Mat ell m → Prop) :
    uniformMass (fun e : Samples ell m => B (right e)) = uniformMass B := by
  have h := Fintype.expect_equiv (stepEquiv ell m)
    (fun e => indicator (B (right e))) (fun e => indicator (B (left e)))
    (fun _ => rfl)
  exact h.trans (left_uniform B)

theorem acceptance_eq {ell m : ℕ} (f : Mat ell m → Vector ell) :
    RowErasure.equalityAcceptance (left (ell := ell) (m := m)) right f =
      Shortcode.equalityAcceptance f := by
  classical
  unfold RowErasure.equalityAcceptance uniformMass Shortcode.equalityAcceptance
  rw [expect_prod]
  apply Finset.expect_congr rfl
  intro M _
  rw [expect_prod]
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro l _
  by_cases h : f M = f (M + rankOne a l)
  · simp [indicator, left, right, h]
  · simp [indicator, left, right, h]

/-- Zero-padding turns the actual bounded-slice inverse conclusion into the
description-based inverse conclusion used by the erasure proof. -/
theorem described_inverse {ell m r : ℕ} (α η : ℝ)
    (inverse : ∀ f : Mat ell m → Vector ell,
      η ≤ Shortcode.equalityAcceptance f → HasAffineSlice f α r) :
    ∀ f : Mat ell m → Vector ell,
      η ≤ RowErasure.equalityAcceptance (left (ell := ell) (m := m)) right f →
        ∃ d : Description ell m r, ((family ell m r).points d).Nonempty ∧
          α ≤ (family ell m r).agreement f d := by
  intro f hf
  rw [acceptance_eq] at hf
  obtain ⟨S, hrows, hcols, hne, z, u, hagree⟩ := inverse f hf
  refine ⟨describe S z u, ?_, ?_⟩
  · change (padSlice S r).points.Nonempty
    simpa only [padSlice_points S hrows hcols] using hne
  · rw [family_agreement]
    simpa only [describe_toSlice, describe_coefficient, describe_intercept,
      padSlice_affineAgreement S hrows hcols] using hagree

/-- Concrete fixed-context advice lower bound. All full matrix and row-map
samples are uniform. The still-required mathematical premises are visible:
the actual shortcode inverse and a simultaneous small-replacement witness. -/
theorem advice_mass_ge_of_inverse_and_erasure {ell m r : ℕ}
    (f : Mat ell m → Vector ell) (η α : ℝ) (hη : 0 < η) (hα : 0 < α)
    (haccept : 4 * η ≤ Shortcode.equalityAcceptance f)
    (inverse : ∀ g : Mat ell m → Vector ell,
      η ≤ Shortcode.equalityAcceptance g → HasAffineSlice g α r)
    (erasure : ∃ replacement : Mat ell m → Vector ell,
      ∀ d : Description ell m r, ((family ell m r).points d).Nonempty →
        (family ell m r).randomizedAgreement
          ((family ell m r).erasedUnion f α) replacement d < α / 4) :
    η / (2 ^ (ell * r) : ℝ) ≤ adviceMass ((family ell m r).goodAt f α) := by
  have hmass := (family ell m r).union_mass_ge_of_inverse_and_erasure
    left right f η α hη hα
    (by simpa only [acceptance_eq] using haccept)
    left_uniform right_uniform (described_inverse α η inverse) erasure
  have h := adviceMass_ge_of_union_mass ((family ell m r).goodAt f α) η hmass
  simpa only [card_rowMap, Nat.cast_pow, Nat.cast_ofNat] using h

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

section

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open scoped BigOperators

noncomputable section

/-- One replacement table simultaneously defeats every padded slice/target.
The budget depends only on dimensions and α, not on the labeling or erased set. -/
theorem exists_replacement_of_budget {ell m r : ℕ}
    (B : Mat ell m → Prop) (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8)
    (hbudget : (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
      Real.exp (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32) < 1) :
    ∃ replacement : Mat ell m → Vector ell,
      ∀ d : Description ell m r, ((family ell m r).points d).Nonempty →
        (family ell m r).randomizedAgreement B replacement d < α / 4 := by
  let ρ := Real.exp (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32)
  apply (family ell m r).exists_erasure_of_probability_bound B α ρ
  · intro d
    by_cases hne : ((family ell m r).points d).Nonempty
    · have htail := (family ell m r).randomizedAgreement_probability_le B α hα hαone
        (by simpa only [card_vector, Nat.cast_pow, Nat.cast_ofNat] using halphabet) d
      have hcardNat := d.toSlice.pow_dimension_le_card r le_rfl le_rfl hne
      have hcard : (2 : ℝ) ^ ((ell - r) * (m - r)) ≤
          (((family ell m r).points d).card : ℝ) := by
        exact_mod_cast hcardNat
      apply htail.trans
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hcard (sq_nonneg α)
      linarith
    · simpa [uniformMass, indicator, hne] using (Real.exp_pos
        (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32)).le
  · simpa only [card_description, Nat.cast_pow, Nat.cast_ofNat] using hbudget

/-- The random-erasure obligation is discharged here by proved finite product
concentration and concrete slice counts. The inverse hypothesis is still the
genuine new-route mathematical input. -/
theorem advice_mass_ge_of_inverse_and_budget {ell m r : ℕ}
    (f : Mat ell m → Vector ell) (η α : ℝ) (hη : 0 < η)
    (hα : 0 < α) (hαone : α ≤ 1)
    (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8)
    (haccept : 4 * η ≤ Shortcode.equalityAcceptance f)
    (inverse : ∀ g : Mat ell m → Vector ell,
      η ≤ Shortcode.equalityAcceptance g → HasAffineSlice g α r)
    (hbudget : (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
      Real.exp (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32) < 1) :
    η / (2 ^ (ell * r) : ℝ) ≤ adviceMass ((family ell m r).goodAt f α) := by
  exact advice_mass_ge_of_inverse_and_erasure f η α hη hα haccept inverse
    (exists_replacement_of_budget ((family ell m r).erasedUnion f α)
      α hα hαone halphabet hbudget)

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

section

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open scoped BigOperators

noncomputable section

/-- A single dimension threshold supplies replacements for every erased set.
There is no inverse-theorem premise in this concentration/counting statement. -/
theorem exists_erasure_threshold (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (ell r : ℕ) (hr : r < ell) (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ B : Mat ell m → Prop,
        ∃ replacement : Mat ell m → Vector ell,
          ∀ d : Description ell m r, ((family ell m r).points d).Nonempty →
            (family ell m r).randomizedAgreement B replacement d < α / 4 := by
  obtain ⟨m₀, hm₀⟩ := exists_unionBound_threshold α hα ell r hr
  refine ⟨m₀, ?_⟩
  intro m hm B
  apply exists_replacement_of_budget B α hα hαone halphabet
  simpa only [neg_mul] using (hm₀ m hm).2

/-- For sufficiently many columns, every accepted function has a positive
measure of good row advice, assuming the genuine bounded-slice inverse. -/
theorem exists_fixed_context_advice_threshold (η α : ℝ)
    (hη : 0 < η) (hα : 0 < α) (hαone : α ≤ 1)
    (ell r : ℕ) (hr : r < ell) (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (∀ g : Mat ell m → Vector ell,
        η ≤ Shortcode.equalityAcceptance g → HasAffineSlice g α r) →
      ∀ f : Mat ell m → Vector ell,
        4 * η ≤ Shortcode.equalityAcceptance f →
          η / (2 ^ (ell * r) : ℝ) ≤ adviceMass ((family ell m r).goodAt f α) := by
  obtain ⟨m₀, hm₀⟩ := exists_erasure_threshold α hα hαone ell r hr halphabet
  refine ⟨m₀, ?_⟩
  intro m hm inverse f haccept
  exact advice_mass_ge_of_inverse_and_erasure f η α hη hα haccept inverse
    (hm₀ m hm ((family ell m r).erasedUnion f α))

theorem exists_contextual_advice_threshold (η α : ℝ)
    (hη : 0 < η) (hα : 0 < α) (hαone : α ≤ 1)
    (ell r : ℕ) (hr : r < ell) (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (∀ g : Mat ell m → Vector ell,
        η ≤ Shortcode.equalityAcceptance g → HasAffineSlice g α r) →
      ∀ (Q : Type) [Fintype Q] (f : Q → Mat ell m → Vector ell),
        10 * η ≤ uniformMass (fun q => 4 * η ≤ Shortcode.equalityAcceptance (f q)) →
          10 * η ^ 2 / (2 ^ (ell * r) : ℝ) ≤
            Finset.univ.expect (fun q => adviceMass ((family ell m r).goodAt (f q) α)) := by
  obtain ⟨m₀, hm₀⟩ := exists_erasure_threshold α hα hαone ell r hr halphabet
  refine ⟨m₀, ?_⟩
  intro m hm inverse Q _ f hcontext
  have hlocal : ∀ q : Q, 4 * η ≤ Shortcode.equalityAcceptance (f q) →
      η ≤ uniformMass (goodUnion ((family ell m r).goodAt (f q) α)) := by
    intro q hq
    exact (family ell m r).union_mass_ge_of_inverse_and_erasure
      left right (f q) η α hη hα
      (by simpa only [acceptance_eq] using hq)
      left_uniform right_uniform (described_inverse α η inverse)
      (hm₀ m hm ((family ell m r).erasedUnion (f q) α))
  have h := advice_average_ge_ten_eta_sq_div_card
    (fun q => 4 * η ≤ Shortcode.equalityAcceptance (f q))
    (fun q => (family ell m r).goodAt (f q) α) η hη.le hcontext hlocal
  simpa only [card_rowMap, Nat.cast_pow, Nat.cast_ofNat] using h

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

section

/-!
Visible selection of a row-erasure witness. The selected description depends
only on the fixed table function, the row map, and the observed row value.
The full sampled matrix enters only the later event testing its membership in
the already selected slice. Classical choice fixes one witness once and for all;
proof irrelevance makes the choice independent of the goodness proof.
-/

namespace UniqueGamesTheorem.Inverse.RowErasure

noncomputable section

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

end
end UniqueGamesTheorem.Inverse.RowErasure

end

section

/-!
Normalize the affine target chosen from visible row advice. The selected row
and column equations are unchanged. Only the target coefficient and intercept
are replaced, with exact target equality on the entire selected slice.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureDescriptions

open UniqueGamesTheorem.Inverse.Shortcode

/-- Replace the affine target while retaining all row and column data. -/
def Description.withTarget {ell m r : ℕ} (d : Description ell m r)
    (z : Vector m) (u : Vector ell) : Description ell m r :=
  (d.1, d.2.1, d.2.2.1, d.2.2.2.1, z, u)

@[simp] theorem Description.withTarget_toSlice {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).toSlice = d.toSlice := rfl

@[simp] theorem Description.withTarget_coefficient {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).coefficient = z := rfl

@[simp] theorem Description.withTarget_intercept {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).intercept = u := rfl

end UniqueGamesTheorem.Inverse.RowErasureDescriptions

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions

noncomputable section

variable {ell m r : ℕ}

/-- Normalization of the already chosen description. The sampled matrix is
absent from the selector's inputs; pointwise target equality holds afterward
for every matrix in the selected slice. -/
theorem exists_normalizedChosenDescription
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    let d₀ := (family ell m r).chosenDescription f α A S hgood
    ∃ d : Description ell m r,
      (family ell m r).rowMap d = A ∧
      (family ell m r).rowValue d = S ∧
      ((family ell m r).points d).Nonempty ∧
      α / 2 ≤ (family ell m r).agreement f d ∧
      e d.coefficient = 1 ∧
      d.toSlice = d₀.toSlice ∧
      (family ell m r).agreement f d = (family ell m r).agreement f d₀ ∧
      ∀ M, M ∈ (family ell m r).points d₀ →
        (family ell m r).target d M = (family ell m r).target d₀ M := by
  classical
  let d₀ := (family ell m r).chosenDescription f α A S hgood
  obtain ⟨hrow, hvalue, hnonempty, hagree⟩ :=
    (family ell m r).chosenDescription_spec f α A S hgood
  obtain ⟨M₀, hM₀⟩ := hnonempty
  have hcontains : d₀.toSlice.Contains M₀ := by
    exact (Finset.mem_filter.mp hM₀).2
  have hagree' : α / 2 ≤ d₀.toSlice.affineAgreement f d₀.coefficient d₀.intercept := by
    exact (family_agreement d₀ f) ▸ hagree
  obtain ⟨z, u, hfirst, heq, htarget⟩ :=
    d₀.toSlice.first_bit_normalization M₀ hcontains e f d₀.coefficient d₀.intercept
      (fun h M => hfold h M) α hα hagree' hsmall
  have heq' : (family ell m r).agreement f (d₀.withTarget z u) =
      (family ell m r).agreement f d₀ := by
    rw [family_agreement, family_agreement]
    exact heq
  refine ⟨d₀.withTarget z u, hrow, hvalue, ⟨M₀, hM₀⟩, ?_, hfirst, rfl, heq', ?_⟩
  · exact heq'.symm ▸ hagree
  · intro M hM
    exact htarget M (Finset.mem_filter.mp hM).2

/-- A fixed normalized witness determined by the visible table and row advice.
All remaining inputs are the fixed normalization functional and proofs. -/
def normalizedChosenDescription
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    Description ell m r :=
  Classical.choose (exists_normalizedChosenDescription f α A S hgood e hfold hα hsmall)

theorem normalizedChosenDescription_spec
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    let d₀ := (family ell m r).chosenDescription f α A S hgood
    let d := normalizedChosenDescription f α A S hgood e hfold hα hsmall
    (family ell m r).rowMap d = A ∧
      (family ell m r).rowValue d = S ∧
      ((family ell m r).points d).Nonempty ∧
      α / 2 ≤ (family ell m r).agreement f d ∧
      e d.coefficient = 1 ∧
      d.toSlice = d₀.toSlice ∧
      (family ell m r).agreement f d = (family ell m r).agreement f d₀ ∧
      ∀ M, M ∈ (family ell m r).points d₀ →
        (family ell m r).target d M = (family ell m r).target d₀ M :=
  Classical.choose_spec
    (exists_normalizedChosenDescription f α A S hgood e hfold hα hsmall)

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

section

/-!
Finite partition estimates for a selector fixed by visible data. The observation
fibers need not have equal sizes. Each local counting inequality is summed over
the actual fibers, then divided by the size of the hidden sample space.
-/

namespace UniqueGamesTheorem.Inverse.RowErasure.SelectionPartition

open scoped BigOperators Classical

noncomputable section

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
      exact (Finset.sum_subset hsub (by
        intro x _ hx
        simp only [ite_eq_right hx])).symm
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

end
end UniqueGamesTheorem.Inverse.RowErasure.SelectionPartition

end

section

/-!
Exact uniform parametrization of the concrete row/column slice.  The quotient
parameter describes every point, not only a lower-bounding subfamily.  Affine
targets retain the base-point contribution and their original intercept.
-/

namespace UniqueGamesTheorem.Inverse.Shortcode.Slice

noncomputable section
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

end
end UniqueGamesTheorem.Inverse.Shortcode.Slice

end

end OAI
