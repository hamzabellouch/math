import Mathlib
import OAI.Computability.MaxCut.Games.Target

namespace OAI

/-! Exact bridges between the integer-encoded target gaps and acceptance rates.
Repeated constraint entries retain their multiplicity in every definition. -/

namespace MaxCutGames.Integration.GapSemantics

open MaxCutGames.Foundations.Target

def errorValue (e : RationalError) : ℚ := (e.numerator : ℚ) / e.denominator

def satisfactionRate {q : Nat} (g : Instance q) (labeling : Fin g.vertices → Fin q) : ℚ :=
  (countSatisfied labeling g.constraints : ℚ) / g.constraints.length

theorem countSatisfied_eq_sum {n q : Nat} (labeling : Fin n → Fin q)
    (constraints : List (Constraint n q)) :
    countSatisfied labeling constraints =
      (constraints.map (fun c => if c.satisfied labeling then (1 : Nat) else 0)).sum := by
  induction constraints with
  | nil => rfl
  | cons c cs ih => simp [countSatisfied, ih]

theorem countSatisfied_ofFn {m n q : Nat} (labeling : Fin n → Fin q)
    (constraints : Fin m → Constraint n q) :
    countSatisfied labeling (List.ofFn constraints) =
      ∑ i, if (constraints i).satisfied labeling then (1 : Nat) else 0 := by
  rw [countSatisfied_eq_sum, List.map_ofFn, List.sum_ofFn]
  rfl

def uniformConstraintAcceptance {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) : ℚ :=
  Finset.univ.expect (fun i : Fin g.constraints.length =>
    if g.constraints[i.val].satisfied labeling then (1 : ℚ) else 0)

/-- Uniform sampling is over occurrence indices, so equal constraints are
counted with exactly their stored multiplicity. -/
theorem uniformConstraintAcceptance_eq_rate {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    uniformConstraintAcceptance g labeling = satisfactionRate g labeling := by
  have hcount := countSatisfied_ofFn labeling
    (fun i : Fin g.constraints.length => g.constraints[i.val])
  rw [List.ofFn_getElem] at hcount
  unfold uniformConstraintAcceptance satisfactionRate
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, hcount]
  congr 1
  simp

theorem errorValue_pos (e : RationalError) : 0 < errorValue e := by
  apply div_pos
  · exact_mod_cast e.numeratorPositive
  · exact_mod_cast e.denominatorPositive

theorem errorValue_lt_half (e : RationalError) : errorValue e < 1 / 2 := by
  have hd : (0 : ℚ) < e.denominator := by exact_mod_cast e.denominatorPositive
  have hn : (2 : ℚ) * e.numerator < e.denominator := by exact_mod_cast e.belowHalf
  unfold errorValue
  apply (div_lt_iff₀ hd).2
  linarith

theorem satisfactionRate_nonneg {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) : 0 ≤ satisfactionRate g labeling := by
  apply div_nonneg <;> exact Nat.cast_nonneg _

theorem satisfactionRate_le_one {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) : satisfactionRate g labeling ≤ 1 := by
  have hm : (0 : ℚ) < g.constraints.length := by
    exact_mod_cast g.constraintCount_positive
  unfold satisfactionRate
  rw [div_le_iff₀ hm, one_mul]
  exact_mod_cast countSatisfied_le_length labeling g.constraints

theorem completeAt_iff {q : Nat} (e : RationalError) (g : Instance q) :
    CompleteAt e g ↔ ∃ labeling, 1 - errorValue e ≤ satisfactionRate g labeling := by
  unfold CompleteAt
  apply exists_congr
  intro labeling
  have hd : (0 : ℚ) < e.denominator := by exact_mod_cast e.denominatorPositive
  have hm : (0 : ℚ) < g.constraints.length := by
    exact_mod_cast g.constraintCount_positive
  have hsub : (1 : ℚ) - (e.numerator : ℚ) / e.denominator =
      ((e.denominator : ℚ) - e.numerator) / e.denominator := by
    rw [sub_div, div_self (ne_of_gt hd)]
  unfold errorValue satisfactionRate
  rw [hsub, div_le_div_iff₀ hd hm]
  constructor
  · intro h
    have hq : (e.denominator : ℚ) * g.constraints.length ≤
        (e.denominator : ℚ) * countSatisfied labeling g.constraints +
          (e.numerator : ℚ) * g.constraints.length := by exact_mod_cast h
    nlinarith
  · intro h
    have hq : (e.denominator : ℚ) * g.constraints.length ≤
        (e.denominator : ℚ) * countSatisfied labeling g.constraints +
          (e.numerator : ℚ) * g.constraints.length := by nlinarith
    exact_mod_cast hq

theorem soundAt_iff {q : Nat} (e : RationalError) (g : Instance q) :
    SoundAt e g ↔ ∀ labeling, satisfactionRate g labeling ≤ errorValue e := by
  unfold SoundAt
  apply forall_congr'
  intro labeling
  have hd : (0 : ℚ) < e.denominator := by exact_mod_cast e.denominatorPositive
  have hm : (0 : ℚ) < g.constraints.length := by
    exact_mod_cast g.constraintCount_positive
  unfold errorValue satisfactionRate
  rw [div_le_div_iff₀ hm hd]
  constructor
  · intro h
    have hq : (e.denominator : ℚ) * countSatisfied labeling g.constraints ≤
        (e.numerator : ℚ) * g.constraints.length := by exact_mod_cast h
    nlinarith
  · intro h
    have hq : (e.denominator : ℚ) * countSatisfied labeling g.constraints ≤
        (e.numerator : ℚ) * g.constraints.length := by nlinarith
    exact_mod_cast hq

/-- Strengthening either error threshold implies the requested weaker gap. -/
theorem completeAt_mono {q : Nat} {e e' : RationalError} {g : Instance q}
    (hee : errorValue e ≤ errorValue e') (hg : CompleteAt e g) : CompleteAt e' g := by
  obtain ⟨labeling, hl⟩ := (completeAt_iff e g).1 hg
  apply (completeAt_iff e' g).2
  exact ⟨labeling, le_trans (sub_le_sub_left hee 1) hl⟩

theorem soundAt_mono {q : Nat} {e e' : RationalError} {g : Instance q}
    (hee : errorValue e ≤ errorValue e') (hg : SoundAt e g) : SoundAt e' g := by
  apply (soundAt_iff e' g).2
  intro labeling
  exact le_trans ((soundAt_iff e g).1 hg labeling) hee

/-- The same target gap is obtained when the analysis uses real expectations. -/
theorem completeAt_iff_real {q : Nat} (e : RationalError) (g : Instance q) :
    CompleteAt e g ↔ ∃ labeling,
      1 - (errorValue e : ℝ) ≤
        (countSatisfied labeling g.constraints : ℝ) / g.constraints.length := by
  rw [completeAt_iff]
  apply exists_congr
  intro labeling
  simpa [satisfactionRate] using
    (Rat.cast_le (K := ℝ) (p := 1 - errorValue e)
      (q := satisfactionRate g labeling)).symm

theorem soundAt_iff_real {q : Nat} (e : RationalError) (g : Instance q) :
    SoundAt e g ↔ ∀ labeling,
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤
        (errorValue e : ℝ) := by
  rw [soundAt_iff]
  apply forall_congr'
  intro labeling
  simpa [satisfactionRate] using
    (Rat.cast_le (K := ℝ) (p := satisfactionRate g labeling) (q := errorValue e)).symm

end MaxCutGames.Integration.GapSemantics

/-! Changing finite encodings preserves the actual Unique Games instance gaps.
Vertex names may be permuted and constraint occurrences may be reordered. -/

namespace MaxCutGames.Integration.InstanceEquivalences

open MaxCutGames.Foundations.Target
open GapSemantics

def renameConstraint {n m q : Nat} (e : Fin n ≃ Fin m) (c : Constraint n q) :
    Constraint m q where
  source := e c.source
  target := e c.target
  permutation := c.permutation

@[simp] theorem renameConstraint_satisfied {n m q : Nat} (e : Fin n ≃ Fin m)
    (c : Constraint n q) (labeling : Fin m → Fin q) :
    (renameConstraint e c).satisfied labeling = c.satisfied (labeling ∘ e) := rfl

theorem rename_count {n m q : Nat} (e : Fin n ≃ Fin m)
    (constraints : List (Constraint n q)) (labeling : Fin m → Fin q) :
    countSatisfied labeling (constraints.map (renameConstraint e)) =
      countSatisfied (labeling ∘ e) constraints := by
  induction constraints with
  | nil => rfl
  | cons c cs ih =>
      by_cases hc : c.satisfied (labeling ∘ e) = true <;> simp [countSatisfied, ih, hc]

def renameInstance {q m : Nat} (g : Instance q) (e : Fin g.vertices ≃ Fin m) :
    Instance q where
  vertices := m
  constraints := g.constraints.map (renameConstraint e)
  nonempty := by
    intro h
    exact g.nonempty (List.map_eq_nil_iff.mp h)

theorem countSatisfied_perm {n q : Nat} (labeling : Fin n → Fin q)
    {constraints constraints' : List (Constraint n q)}
    (h : constraints.Perm constraints') :
    countSatisfied labeling constraints = countSatisfied labeling constraints' := by
  rw [countSatisfied_eq_sum, countSatisfied_eq_sum]
  exact (h.map (fun c => if c.satisfied labeling then (1 : Nat) else 0)).sum_eq

/-- This statement is directly usable by an executable adapter: only its
vertex equivalence and its permutation of the explicit edge list are needed. -/
theorem satisfactionRate_eq_of_rename_perm {q : Nat} (g h : Instance q)
    (e : Fin g.vertices ≃ Fin h.vertices)
    (hp : h.constraints.Perm (g.constraints.map (renameConstraint e)))
    (labeling : Fin h.vertices → Fin q) :
    satisfactionRate h labeling = satisfactionRate g (labeling ∘ e) := by
  have hcount := countSatisfied_perm labeling hp
  rw [rename_count] at hcount
  have hlength := hp.length_eq
  simp only [List.length_map] at hlength
  unfold satisfactionRate
  rw [hcount, hlength]

theorem completeAt_iff_of_rename_perm {q : Nat} (error : RationalError)
    (g h : Instance q) (e : Fin g.vertices ≃ Fin h.vertices)
    (hp : h.constraints.Perm (g.constraints.map (renameConstraint e))) :
    CompleteAt error h ↔ CompleteAt error g := by
  rw [completeAt_iff, completeAt_iff]
  constructor
  · rintro ⟨labeling, hl⟩
    refine ⟨labeling ∘ e, ?_⟩
    rwa [satisfactionRate_eq_of_rename_perm g h e hp] at hl
  · rintro ⟨labeling, hl⟩
    refine ⟨labeling ∘ e.symm, ?_⟩
    rw [satisfactionRate_eq_of_rename_perm g h e hp]
    simpa [Function.comp_def] using hl

theorem soundAt_iff_of_rename_perm {q : Nat} (error : RationalError)
    (g h : Instance q) (e : Fin g.vertices ≃ Fin h.vertices)
    (hp : h.constraints.Perm (g.constraints.map (renameConstraint e))) :
    SoundAt error h ↔ SoundAt error g := by
  rw [soundAt_iff, soundAt_iff]
  constructor
  · intro hs labeling
    have hl := hs (labeling ∘ e.symm)
    rw [satisfactionRate_eq_of_rename_perm g h e hp] at hl
    simpa [Function.comp_def] using hl
  · intro hs labeling
    rw [satisfactionRate_eq_of_rename_perm g h e hp]
    exact hs (labeling ∘ e)

theorem rename_rate {q m : Nat} (g : Instance q) (e : Fin g.vertices ≃ Fin m)
    (labeling : Fin m → Fin q) :
    satisfactionRate (renameInstance g e) labeling = satisfactionRate g (labeling ∘ e) :=
  satisfactionRate_eq_of_rename_perm g (renameInstance g e) e (.refl _) labeling

theorem completeAt_rename_iff {q m : Nat} (error : RationalError)
    (g : Instance q) (e : Fin g.vertices ≃ Fin m) :
    CompleteAt error (renameInstance g e) ↔ CompleteAt error g :=
  completeAt_iff_of_rename_perm error g (renameInstance g e) e (.refl _)

theorem soundAt_rename_iff {q m : Nat} (error : RationalError)
    (g : Instance q) (e : Fin g.vertices ≃ Fin m) :
    SoundAt error (renameInstance g e) ↔ SoundAt error g :=
  soundAt_iff_of_rename_perm error g (renameInstance g e) e (.refl _)

end MaxCutGames.Integration.InstanceEquivalences

end OAI
