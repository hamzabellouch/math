import Mathlib
import OAI.Computability.DirectedFeedback.Games.PositiveMultiplier

namespace OAI

namespace DFVSGames.Inverse.RowErasure

open scoped BigOperators

noncomputable section

variable {X Y A S D : Type*}

structure SliceFamily (X Y A S D : Type*) where
  advice : A → X → S
  rowMap : D → A
  rowValue : D → S
  points : D → Finset X
  target : D → X → Y
  points_row : ∀ d x, x ∈ points d → advice (rowMap d) x = rowValue d

def SliceFamily.agreement (F : SliceFamily X Y A S D) (f : X → Y) (d : D) : ℝ :=
  (F.points d).expect fun x => indicator (f x = F.target d x)

def SliceFamily.GoodAdvice (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Prop :=
  ∃ d, F.rowMap d = a ∧ F.rowValue d = s ∧ (F.points d).Nonempty ∧
    α / 2 ≤ F.agreement f d

def SliceFamily.goodAt (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  F.GoodAdvice f α a (F.advice a x)

def SliceFamily.erasedUnion (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) : X → Prop :=
  goodUnion (F.goodAt f α)

def SliceFamily.randomizedAgreement (F : SliceFamily X Y A S D)
    (B : X → Prop) (replacement : X → Y) (d : D) : ℝ :=
  (F.points d).expect fun x => indicator (B x ∧ replacement x = F.target d x)

theorem SliceFamily.mem_erasedUnion_of_good_row
    (F : SliceFamily X Y A S D) (f : X → Y) (α : ℝ) (d : D)
    (good : F.GoodAdvice f α (F.rowMap d) (F.rowValue d))
    {x : X} (hx : x ∈ F.points d) : F.erasedUnion f α x := by
  refine ⟨F.rowMap d, ?_⟩
  change F.GoodAdvice f α (F.rowMap d) (F.advice (F.rowMap d) x)
  rw [F.points_row d x hx]
  exact good

theorem SliceFamily.original_agreement_lt_of_not_good
    (F : SliceFamily X Y A S D) (f : X → Y) (α : ℝ) (d : D)
    (hne : (F.points d).Nonempty)
    (not_good : ¬ F.GoodAdvice f α (F.rowMap d) (F.rowValue d)) :
    F.agreement f d < α / 2 := by
  by_contra h
  exact not_good ⟨d, rfl, rfl, hne, le_of_not_gt h⟩

theorem SliceFamily.modified_agreement_le_original_add_randomized
    (F : SliceFamily X Y A S D) (B : X → Prop)
    (f replacement : X → Y) (d : D) :
    F.agreement (replaceOn B f replacement) d ≤
      F.agreement f d + F.randomizedAgreement B replacement d := by
  classical
  have h := Finset.expect_le_expect (s := F.points d)
    (f := fun x => indicator (replaceOn B f replacement x = F.target d x))
    (g := fun x => indicator (f x = F.target d x) +
      indicator (B x ∧ replacement x = F.target d x)) (by
      intro x _
      by_cases hx : B x
      · rw [replaceOn_of_mem B f replacement hx]
        simp only [indicator, hx, true_and]
        have hnonneg := indicator_nonneg (f x = F.target d x)
        unfold indicator at hnonneg
        linarith
      · rw [replaceOn_of_not_mem B f replacement hx]
        simp [indicator, hx])
  simpa only [Finset.expect_add_distrib, SliceFamily.agreement,
    SliceFamily.randomizedAgreement] using h

theorem SliceFamily.modified_agreement_eq_randomized_of_good
    (F : SliceFamily X Y A S D) (f replacement : X → Y)
    (α : ℝ) (d : D)
    (good : F.GoodAdvice f α (F.rowMap d) (F.rowValue d)) :
    F.agreement (replaceOn (F.erasedUnion f α) f replacement) d =
      F.randomizedAgreement (F.erasedUnion f α) replacement d := by
  classical
  apply Finset.expect_congr rfl
  intro x hx
  have hB := F.mem_erasedUnion_of_good_row f α d good hx
  rw [replaceOn_of_mem _ f replacement hB]
  simp [indicator, hB]

theorem SliceFamily.modified_agreement_lt
    (F : SliceFamily X Y A S D) (f replacement : X → Y)
    (α : ℝ) (hα : 0 < α)
    (randomized_small : ∀ d, (F.points d).Nonempty →
      F.randomizedAgreement (F.erasedUnion f α) replacement d < α / 4)
    (d : D) (hne : (F.points d).Nonempty) :
    F.agreement (replaceOn (F.erasedUnion f α) f replacement) d < α := by
  classical
  by_cases hg : F.GoodAdvice f α (F.rowMap d) (F.rowValue d)
  · rw [F.modified_agreement_eq_randomized_of_good f replacement α d hg]
    have h := randomized_small d hne
    linarith
  · have ho := F.original_agreement_lt_of_not_good f α d hne hg
    have hr := randomized_small d hne
    have hm := F.modified_agreement_le_original_add_randomized
      (F.erasedUnion f α) f replacement d
    linarith

theorem SliceFamily.union_mass_ge_of_inverse_and_erasure
    {E : Type*} [Fintype X] [Fintype E]
    (F : SliceFamily X Y A S D) (left right : E → X)
    (f : X → Y) (η α : ℝ) (hη : 0 < η) (hα : 0 < α)
    (acceptance_large : 4 * η ≤ equalityAcceptance left right f)
    (left_uniform : ∀ B : X → Prop,
      uniformMass (fun e => B (left e)) = uniformMass B)
    (right_uniform : ∀ B : X → Prop,
      uniformMass (fun e => B (right e)) = uniformMass B)
    (inverse : ∀ g : X → Y, η ≤ equalityAcceptance left right g →
      ∃ d, (F.points d).Nonempty ∧ α ≤ F.agreement g d)
    (erasure : ∃ replacement : X → Y, ∀ d, (F.points d).Nonempty →
      F.randomizedAgreement (F.erasedUnion f α) replacement d < α / 4) :
    η ≤ uniformMass (F.erasedUnion f α) := by
  by_contra h
  have hsmall : uniformMass (F.erasedUnion f α) < η := lt_of_not_ge h
  obtain ⟨replacement, hr⟩ := erasure
  have hmodified := acceptance_ge_original_sub_two_mass left right
    (F.erasedUnion f α) f replacement
    (left_uniform (F.erasedUnion f α)) (right_uniform (F.erasedUnion f α))
  have haccept : η ≤ equalityAcceptance left right
      (replaceOn (F.erasedUnion f α) f replacement) := by linarith
  obtain ⟨d, hne, hd⟩ := inverse _ haccept
  have hlt := F.modified_agreement_lt f replacement α hα hr d hne
  linarith

end
end DFVSGames.Inverse.RowErasure

namespace DFVSGames.Inverse.RowErasure

open scoped BigOperators Classical

noncomputable section

theorem uniformMass_exists_le_sum
    {R D : Type*} [Fintype R] [Fintype D] (bad : D → R → Prop) :
    uniformMass (fun r => ∃ d, bad d r) ≤ ∑ d, uniformMass (bad d) := by
  classical
  have hp : ∀ r, indicator (∃ d, bad d r) ≤ ∑ d, indicator (bad d r) := by
    intro r
    by_cases hr : ∃ d, bad d r
    · obtain ⟨d, hd⟩ := hr
      have h := Finset.single_le_sum
        (s := (Finset.univ : Finset D)) (f := fun d => indicator (bad d r))
        (fun d _ => indicator_nonneg (bad d r)) (Finset.mem_univ d)
      simpa [indicator, hd, show ∃ d, bad d r from ⟨d, hd⟩] using h
    · simp only [indicator, ite_eq_right hr]
      exact Finset.sum_nonneg fun d _ => indicator_nonneg (bad d r)
  have h := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hp r)
  simpa only [uniformMass, Finset.expect_sum_comm] using h

theorem exists_avoiding_of_sum_bad_lt_one
    {R D : Type*} [Fintype R] [Nonempty R] [Fintype D]
    (bad : D → R → Prop) (hsmall : (∑ d, uniformMass (bad d)) < 1) :
    ∃ r, ∀ d, ¬ bad d r := by
  classical
  by_contra h
  have hall : ∀ r, ∃ d, bad d r := by
    intro r
    by_contra hr
    exact h ⟨r, fun d hd => hr ⟨d, hd⟩⟩
  have hm : uniformMass (fun r => ∃ d, bad d r) = 1 := by
    simp [uniformMass, indicator, hall]
  have hb := uniformMass_exists_le_sum bad
  rw [hm] at hb
  linarith

theorem exists_avoiding_of_card_mul_bound_lt_one
    {R D : Type*} [Fintype R] [Nonempty R] [Fintype D]
    (bad : D → R → Prop) (ρ : ℝ)
    (hprob : ∀ d, uniformMass (bad d) ≤ ρ)
    (hsmall : (Fintype.card D : ℝ) * ρ < 1) :
    ∃ r, ∀ d, ¬ bad d r := by
  apply exists_avoiding_of_sum_bad_lt_one bad
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset D)) (fun d _ => hprob d)
  have hsum : (∑ d, uniformMass (bad d)) ≤ (Fintype.card D : ℝ) * ρ := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  exact hsum.trans_lt hsmall

theorem SliceFamily.exists_erasure_of_probability_bound
    {X Y A S D : Type*} [Fintype X] [Fintype Y] [Nonempty Y] [Fintype D]
    (F : SliceFamily X Y A S D) (B : X → Prop) (α ρ : ℝ)
    (hprob : ∀ d, uniformMass (fun replacement : X → Y =>
      (F.points d).Nonempty ∧ α / 4 ≤ F.randomizedAgreement B replacement d) ≤ ρ)
    (hsmall : (Fintype.card D : ℝ) * ρ < 1) :
    ∃ replacement : X → Y, ∀ d, (F.points d).Nonempty →
      F.randomizedAgreement B replacement d < α / 4 := by
  obtain ⟨replacement, hr⟩ := exists_avoiding_of_card_mul_bound_lt_one
    (fun d replacement =>
      (F.points d).Nonempty ∧ α / 4 ≤ F.randomizedAgreement B replacement d)
    ρ hprob hsmall
  refine ⟨replacement, fun d hd => ?_⟩
  exact lt_of_not_ge (fun h => hr d ⟨hd, h⟩)

theorem advice_average_ge
    {Q A X : Type*} [Fintype Q] [Fintype A] [Nonempty A] [Fintype X]
    (goodContext : Q → Prop) (good : Q → A → X → Prop)
    (β η : ℝ) (hη : 0 ≤ η)
    (hcontext : β ≤ uniformMass goodContext)
    (hlocal : ∀ q, goodContext q → η ≤ uniformMass (goodUnion (good q))) :
    β * (η / (Fintype.card A : ℝ)) ≤
      Finset.univ.expect (fun q => adviceMass (good q)) := by
  classical
  have hc : 0 ≤ η / (Fintype.card A : ℝ) :=
    div_nonneg hη (Nat.cast_nonneg _)
  have hp : ∀ q,
      indicator (goodContext q) * (η / (Fintype.card A : ℝ)) ≤ adviceMass (good q) := by
    intro q
    by_cases hq : goodContext q
    · simpa [indicator, hq] using adviceMass_ge_of_union_mass (good q) η (hlocal q hq)
    · simpa [indicator, hq] using adviceMass_nonneg (good q)
  have he := Finset.expect_le_expect (s := Finset.univ) (fun q _ => hp q)
  rw [← Finset.expect_mul] at he
  exact (mul_le_mul_of_nonneg_right hcontext hc).trans he

theorem advice_average_ge_ten_eta_sq_div_card
    {Q A X : Type*} [Fintype Q] [Fintype A] [Nonempty A] [Fintype X]
    (goodContext : Q → Prop) (good : Q → A → X → Prop)
    (η : ℝ) (hη : 0 ≤ η)
    (hcontext : 10 * η ≤ uniformMass goodContext)
    (hlocal : ∀ q, goodContext q → η ≤ uniformMass (goodUnion (good q))) :
    10 * η ^ 2 / (Fintype.card A : ℝ) ≤
      Finset.univ.expect (fun q => adviceMass (good q)) := by
  have h := advice_average_ge goodContext good (10 * η) η hη hcontext hlocal
  convert h using 1 ; ring

end
end DFVSGames.Inverse.RowErasure

namespace DFVSGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical

abbrev F2 := ZMod 2
abbrev Vector (n : ℕ) := Fin n → F2
abbrev Mat (ell m : ℕ) := Matrix (Fin ell) (Fin m) F2

def rankOne {ell m : ℕ} (a : Vector ell) (l : Vector m) : Mat ell m :=
  fun i j => a i * l j

def evaluate {ell m : ℕ} (M : Mat ell m) (z : Vector m) : Vector ell :=
  fun i => ∑ j, M i j * z j

@[simp] theorem evaluate_zero {ell m : ℕ} (M : Mat ell m) : evaluate M 0 = 0 := by
  ext i
  simp [evaluate]

@[simp] theorem rankOne_zero_left {ell m : ℕ} (l : Vector m) :
    rankOne (0 : Vector ell) l = 0 := by
  ext i j
  simp [rankOne]

@[simp] theorem rankOne_zero_right {ell m : ℕ} (a : Vector ell) :
    rankOne a (0 : Vector m) = 0 := by
  ext i j
  simp [rankOne]

def equalityAcceptance {ell m : ℕ} (f : Mat ell m → Vector ell) : ℝ :=
  𝔼 M, 𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then 1 else 0

structure Slice (ell m : ℕ) where
  rows : ℕ
  columns : ℕ
  rowCoefficient : Fin rows → Vector ell
  rowValue : Fin rows → Vector m
  columnCoefficient : Fin columns → Vector m
  columnValue : Fin columns → Vector ell

def Slice.Contains {ell m : ℕ} (S : Slice ell m) (M : Mat ell m) : Prop :=
  (∀ i j, (∑ a, S.rowCoefficient i a * M a j) = S.rowValue i j) ∧
    ∀ i, evaluate M (S.columnCoefficient i) = S.columnValue i

def Slice.points {ell m : ℕ} (S : Slice ell m) : Finset (Mat ell m) :=
  Finset.univ.filter S.Contains

def Slice.affineAgreement {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell) : ℝ :=
  S.points.expect fun M => if f M = evaluate M z + u then 1 else 0

def Slice.constantAgreement {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (u : Vector ell) : ℝ :=
  S.points.expect fun M => if f M = u then 1 else 0

theorem Slice.constantAgreement_eq_affine {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (u : Vector ell) :
    S.constantAgreement f u = S.affineAgreement f 0 u := by
  simp [Slice.constantAgreement, Slice.affineAgreement]

def HasAffineSlice {ell m : ℕ} (f : Mat ell m → Vector ell) (α : ℝ) (r : ℕ) : Prop :=
  ∃ S : Slice ell m, S.rows ≤ r ∧ S.columns ≤ r ∧ S.points.Nonempty ∧
    ∃ z : Vector m, ∃ u : Vector ell, α ≤ S.affineAgreement f z u

theorem hasAffineSlice_of_constant {ell m : ℕ} (f : Mat ell m → Vector ell)
    (α : ℝ) (r : ℕ) (S : Slice ell m) (hrows : S.rows ≤ r)
    (hcolumns : S.columns ≤ r) (hne : S.points.Nonempty) (u : Vector ell)
    (h : α ≤ S.constantAgreement f u) : HasAffineSlice f α r := by
  exact ⟨S, hrows, hcolumns, hne, 0, u, by
    simpa only [S.constantAgreement_eq_affine f u] using h⟩

def InversePrinciple : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∃ r : ℕ, 1 ≤ r ∧
      ∃ ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
          ∀ f : Mat ell m → Vector ell,
            η ≤ equalityAcceptance f → HasAffineSlice f α r

end
end DFVSGames.Inverse.Shortcode

namespace DFVSGames.Inverse.RowErasureDescriptions

open DFVSGames.Inverse.Shortcode
open scoped BigOperators

noncomputable section

abbrev RowMap (ell r : ℕ) := Fin r → Vector ell

abbrev Description (ell m r : ℕ) :=
  (Fin r → Vector ell) × (Fin r → Vector m) ×
    (Fin r → Vector m) × (Fin r → Vector ell) × Vector m × Vector ell

theorem card_vector (n : ℕ) : Fintype.card (Vector n) = 2 ^ n := by
  simp [Shortcode.Vector, F2]

theorem card_rowMap (ell r : ℕ) : Fintype.card (RowMap ell r) = 2 ^ (ell * r) := by
  simp [RowMap, ← pow_mul]

theorem card_description (ell m r : ℕ) :
    Fintype.card (Description ell m r) = 2 ^ ((2 * r + 1) * (ell + m)) := by
  simp only [Description, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ← pow_mul, ← pow_add]
  congr 1
  ring

def Description.toSlice {ell m r : ℕ} (d : Description ell m r) : Slice ell m where
  rows := r
  columns := r
  rowCoefficient := d.1
  rowValue := d.2.1
  columnCoefficient := d.2.2.1
  columnValue := d.2.2.2.1

def Description.coefficient {ell m r : ℕ} (d : Description ell m r) : Vector m :=
  d.2.2.2.2.1

def Description.intercept {ell m r : ℕ} (d : Description ell m r) : Vector ell :=
  d.2.2.2.2.2

def padZero {n r : ℕ} {V : Type*} [Zero V] (f : Fin n → V) : Fin r → V :=
  fun i => if h : i.val < n then f ⟨i.val, h⟩ else 0

def padSlice {ell m : ℕ} (S : Slice ell m) (r : ℕ) : Slice ell m where
  rows := r
  columns := r
  rowCoefficient := padZero S.rowCoefficient
  rowValue := padZero S.rowValue
  columnCoefficient := padZero S.columnCoefficient
  columnValue := padZero S.columnValue

theorem padSlice_contains_iff {ell m r : ℕ} (S : Slice ell m)
    (hrows : S.rows ≤ r) (hcols : S.columns ≤ r) (M : Mat ell m) :
    (padSlice S r).Contains M ↔ S.Contains M := by
  classical
  constructor
  · rintro ⟨hr, hc⟩
    constructor
    · intro i j
      have h := hr ⟨i.val, lt_of_lt_of_le i.isLt hrows⟩ j
      simpa [padSlice, padZero, i.isLt] using h
    · intro i
      have h := hc ⟨i.val, lt_of_lt_of_le i.isLt hcols⟩
      simpa [padSlice, padZero, i.isLt] using h
  · rintro ⟨hr, hc⟩
    constructor
    · intro i j
      by_cases hi : i.val < S.rows
      · simpa [padSlice, padZero, hi] using hr ⟨i.val, hi⟩ j
      · simp [padSlice, padZero, hi]
    · intro i
      by_cases hi : i.val < S.columns
      · simpa [padSlice, padZero, hi] using hc ⟨i.val, hi⟩
      · simp [padSlice, padZero, hi]

theorem padSlice_points {ell m r : ℕ} (S : Slice ell m)
    (hrows : S.rows ≤ r) (hcols : S.columns ≤ r) :
    (padSlice S r).points = S.points := by
  classical
  ext M
  simp [Slice.points, padSlice_contains_iff S hrows hcols M]

theorem padSlice_affineAgreement {ell m r : ℕ} (S : Slice ell m)
    (hrows : S.rows ≤ r) (hcols : S.columns ≤ r)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell) :
    (padSlice S r).affineAgreement f z u = S.affineAgreement f z u := by
  simp only [Slice.affineAgreement, padSlice_points S hrows hcols]

def describe {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) : Description ell m r :=
  (padZero S.rowCoefficient, padZero S.rowValue,
    padZero S.columnCoefficient, padZero S.columnValue, z, u)

@[simp] theorem describe_toSlice {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) :
    (describe (r := r) S z u).toSlice = padSlice S r := rfl

@[simp] theorem describe_coefficient {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) : (describe (r := r) S z u).coefficient = z := rfl

@[simp] theorem describe_intercept {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) : (describe (r := r) S z u).intercept = u := rfl

theorem exists_description {ell m r : ℕ} (S : Slice ell m)
    (hrows : S.rows ≤ r) (hcols : S.columns ≤ r)
    (z : Vector m) (u : Vector ell) :
    ∃ d : Description ell m r, d.toSlice.points = S.points ∧
      d.coefficient = z ∧ d.intercept = u := by
  refine ⟨describe S z u, ?_, rfl, rfl⟩
  exact padSlice_points S hrows hcols

end
end DFVSGames.Inverse.RowErasureDescriptions

namespace DFVSGames.Inverse.RowErasureMatrix

open DFVSGames.Inverse.Shortcode
open DFVSGames.Inverse.RowErasure
open DFVSGames.Inverse.RowErasureDescriptions
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
end DFVSGames.Inverse.RowErasureMatrix

namespace DFVSGames.Inverse.AffineWitness

abbrev F2 := ZMod 2

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

theorem add_self_binary (c : C) : c + c = 0 := by
  have h : (1 : F2) + 1 = 0 := by decide
  calc
    c + c = (1 : F2) • c + (1 : F2) • c := by simp
    _ = ((1 : F2) + 1) • c := (add_smul _ _ _).symm
    _ = 0 := by rw [h, zero_smul]

def InSlice (A : C →ₗ[F2] R) (Z : Submodule F2 D)
    (M₀ M : D →ₗ[F2] C) : Prop :=
  A.comp M = A.comp M₀ ∧ ∀ w ∈ Z, M w = M₀ w

theorem translate_target (A : C →ₗ[F2] R) (Z : Submodule F2 D)
    (M₀ M : D →ₗ[F2] C) (hM : InSlice A Z M₀ M)
    (z w : D) (hw : w ∈ Z) (u : C) :
    M (z + w) + (u + M₀ w) = M z + u := by
  rw [map_add, hM.2 w hw]
  calc
    (M z + M₀ w) + (u + M₀ w) = (M z + u) + (M₀ w + M₀ w) := by
      ac_rfl
    _ = M z + u := by rw [add_self_binary, add_zero]

theorem no_affine_representative (e : D →ₗ[F2] F2) (Z : Submodule F2 D)
    (z : D) (h : ¬ ∃ w ∈ Z, e (z + w) = 1) :
    e z = 0 ∧ ∀ w ∈ Z, e w = 0 := by
  have scalar_cases : ∀ a : F2, a = 0 ∨ a = 1 := by decide
  have hz : e z = 0 := by
    rcases scalar_cases (e z) with hz | hz
    · exact hz
    · exact False.elim (h ⟨0, Z.zero_mem, by simpa using hz⟩)
  refine ⟨hz, ?_⟩
  intro w hw
  rcases scalar_cases (e w) with hw0 | hw1
  · exact hw0
  · exact False.elim (h ⟨w, hw, by rw [map_add, hz, zero_add, hw1]⟩)

def shift (e : D →ₗ[F2] F2) (h : C) (M : D →ₗ[F2] C) : D →ₗ[F2] C :=
  M + e.smulRight h

@[simp] theorem shift_apply (e : D →ₗ[F2] F2) (h : C)
    (M : D →ₗ[F2] C) (x : D) : shift e h M x = M x + e x • h := rfl

@[simp] theorem shift_zero (e : D →ₗ[F2] F2) (M : D →ₗ[F2] C) :
    shift e 0 M = M := by
  ext x
  simp

theorem shift_add (e : D →ₗ[F2] F2) (h k : C) (M : D →ₗ[F2] C) :
    shift e (h + k) M = shift e h (shift e k M) := by
  ext x
  simp only [shift_apply, smul_add]
  ac_rfl

theorem shift_preserves_slice (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ M : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (h : A.ker) (hM : InSlice A Z M₀ M) :
    InSlice A Z M₀ (shift e h M) := by
  constructor
  · ext x
    have hx := LinearMap.congr_fun hM.1 x
    have hh : A (h : C) = 0 := h.property
    simpa only [LinearMap.comp_apply, shift_apply, map_add, map_smul,
      hh, smul_zero, add_zero] using hx
  · intro w hw
    simp only [shift_apply, heZ w hw, zero_smul, add_zero]
    exact hM.2 w hw

theorem shift_preserves_target (e : D →ₗ[F2] F2) (z : D) (hz : e z = 0)
    (u h : C) (M : D →ₗ[F2] C) :
    shift e h M z + u = M z + u := by
  simp only [shift_apply, hz, zero_smul, add_zero]

theorem normalize (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (h : ∃ w ∈ Z, e (z + w) = 1) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  obtain ⟨w, hw, he⟩ := h
  exact ⟨z + w, u + M₀ w, he, fun M hM => translate_target A Z M₀ M hM z w hw u⟩

end DFVSGames.Inverse.AffineWitness

namespace DFVSGames.Inverse.AffineWitness

variable {D C R ι : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

theorem columns_iff_span (q : ι → D) (t : ι → C)
    (M₀ M : D →ₗ[F2] C) (hM₀ : ∀ i, M₀ (q i) = t i) :
    (∀ i, M (q i) = t i) ↔
      ∀ w ∈ Submodule.span F2 (Set.range q), M w = M₀ w := by
  constructor
  · intro hM w hw

    apply LinearMap.eqOn_span (s := Set.range q) (x := w) ?_ hw
    rintro _ ⟨i, rfl⟩
    exact (hM i).trans (hM₀ i).symm
  · intro hM i
    exact (hM (q i) (Submodule.subset_span ⟨i, rfl⟩)).trans (hM₀ i)

theorem explicit_slice_iff (A : C →ₗ[F2] R) (S₀ : D →ₗ[F2] R)
    (q : ι → D) (t : ι → C) (M₀ M : D →ₗ[F2] C)
    (hrow : A.comp M₀ = S₀) (hcol : ∀ i, M₀ (q i) = t i) :
    (A.comp M = S₀ ∧ ∀ i, M (q i) = t i) ↔
      InSlice A (Submodule.span F2 (Set.range q)) M₀ M := by
  unfold InSlice
  rw [hrow, columns_iff_span q t M₀ M hcol]

theorem translate_explicit_target (A : C →ₗ[F2] R) (S₀ : D →ₗ[F2] R)
    (q : ι → D) (t : ι → C) (M₀ M : D →ₗ[F2] C)
    (hrow₀ : A.comp M₀ = S₀) (hcol₀ : ∀ i, M₀ (q i) = t i)
    (hrow : A.comp M = S₀) (hcol : ∀ i, M (q i) = t i)
    (z w : D) (hw : w ∈ Submodule.span F2 (Set.range q)) (u : C) :
    M (z + w) + (u + M₀ w) = M z + u :=
  translate_target A _ M₀ M
    ((explicit_slice_iff A S₀ q t M₀ M hrow₀ hcol₀).mp ⟨hrow, hcol⟩) z w hw u

end DFVSGames.Inverse.AffineWitness

namespace DFVSGames.Inverse

variable {H X Y : Type*} [AddGroup H] [AddGroup Y]

theorem folded_action_injective
    (shift : H → X → X)
    (shift_zero : ∀ x, shift 0 x = x)
    (shift_add : ∀ h k x, shift (h + k) x = shift h (shift k x))
    (embed : H → Y) (embed_injective : Function.Injective embed)
    (F target : X → Y)
    (folded : ∀ h x, F (shift h x) = F x + embed h)
    (target_invariant : ∀ h x, target (shift h x) = target x) :
    Function.Injective
      (fun a : H × {x : X // F x = target x} => shift a.1 a.2.val) := by
  intro a b hab
  have htarget : target a.2.val = target b.2.val := by
    calc
      target a.2.val = target (shift a.1 a.2.val) :=
        (target_invariant a.1 a.2.val).symm
      _ = target (shift b.1 b.2.val) := congrArg target hab
      _ = target b.2.val := target_invariant b.1 b.2.val
  have hfold : F a.2.val + embed a.1 = F b.2.val + embed b.1 := by
    calc
      F a.2.val + embed a.1 = F (shift a.1 a.2.val) :=
        (folded a.1 a.2.val).symm
      _ = F (shift b.1 b.2.val) := congrArg F hab
      _ = F b.2.val + embed b.1 := folded b.1 b.2.val
  rw [a.2.property, b.2.property, htarget] at hfold
  have hh : a.1 = b.1 := embed_injective (add_left_cancel hfold)
  have hx : a.2.val = b.2.val := by
    have hshift : shift a.1 a.2.val = shift a.1 b.2.val := by
      simpa only [hh] using hab
    have hinverse := congrArg (shift (-a.1)) hshift
    simpa only [← shift_add, neg_add_cancel, shift_zero] using hinverse
  exact Prod.ext hh (Subtype.ext hx)

theorem folded_action_card_mul_agreement_le
    [Fintype H] [Fintype X] [DecidableEq Y]
    (shift : H → X → X)
    (shift_zero : ∀ x, shift 0 x = x)
    (shift_add : ∀ h k x, shift (h + k) x = shift h (shift k x))
    (embed : H → Y) (embed_injective : Function.Injective embed)
    (F target : X → Y)
    (folded : ∀ h x, F (shift h x) = F x + embed h)
    (target_invariant : ∀ h x, target (shift h x) = target x) :
    Fintype.card H * Fintype.card {x : X // F x = target x} ≤
      Fintype.card X := by
  simpa only [Fintype.card_prod] using
    Fintype.card_le_of_injective
      (fun a : H × {x : X // F x = target x} => shift a.1 a.2.val)
      (folded_action_injective shift shift_zero shift_add embed embed_injective
        F target folded target_invariant)

end DFVSGames.Inverse

end OAI
