import Mathlib
import OAI.Computability.MaxCut.Games.DyadicErrors
import OAI.Computability.MaxCut.Machines.Machine2

namespace OAI

/-! The arbitrary-real-error target and its exact passage from encoded rational
gap reductions. The same formula map and actual machine certificate are reused;
choosing smaller error tolerances does not change the computation. -/

namespace MaxCutGames.Integration.RealTarget

open MaxCutGames.Foundations
open Target

/-- A fixed-alphabet gap reduction from 3SAT, including its actual finite-machine
polynomial runtime, with the two approximation thresholds expressed over ℝ. -/
structure PolynomialGapReduction (ε δ : ℝ) where
  alphabet : Nat
  alphabetAtLeastTwo : 2 ≤ alphabet
  reduce : Formula → Instance alphabet
  computation : Turing.TM2ComputableInPolyTime Complexity.formulaEncoding.encode
    (Complexity.gameEncoding alphabet).encode reduce
  completeness : ∀ formula : Formula, formula.Satisfiable →
    ∃ labeling, 1 - ε ≤
      (countSatisfied labeling (reduce formula).constraints : ℝ) /
        (reduce formula).constraints.length
  soundness : ∀ formula : Formula, ¬ formula.Satisfiable →
    ∀ labeling, (countSatisfied labeling (reduce formula).constraints : ℝ) /
      (reduce formula).constraints.length ≤ δ

/-- A genuine rational-error certificate supplies every weaker real threshold.
The input and output encodings and finite transition program remain identical. -/
def ofRational {e d : RationalError} {ε δ : ℝ}
    (p : Complexity.PolynomialGapReduction e d)
    (hε : (GapSemantics.errorValue e : ℝ) ≤ ε)
    (hδ : (GapSemantics.errorValue d : ℝ) ≤ δ) : PolynomialGapReduction ε δ where
  alphabet := p.alphabet
  alphabetAtLeastTwo := p.alphabetAtLeastTwo
  reduce := p.reduce
  computation := p.computation
  completeness formula hformula := by
    obtain ⟨labeling, hlabel⟩ :=
      (GapSemantics.completeAt_iff_real e (p.reduce formula)).mp
        (p.completeness formula hformula)
    exact ⟨labeling, (sub_le_sub_left hε 1).trans hlabel⟩
  soundness formula hformula labeling :=
    ((GapSemantics.soundAt_iff_real d (p.reduce formula)).mp
      (p.soundness formula hformula) labeling).trans hδ

/-- It suffices to construct the full machine-backed reduction for dyadic
errors. This theorem does not assert that those certificates have been built. -/
theorem for_all_real_of_dyadic
    (certificates : ∀ m n : Nat, Nonempty
      (Complexity.PolynomialGapReduction
        (DyadicErrors.dyadicError m) (DyadicErrors.dyadicError n)))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    Nonempty (PolynomialGapReduction ε δ) := by
  obtain ⟨m, hm⟩ := DyadicErrors.exists_dyadic_below_real hε
  obtain ⟨n, hn⟩ := DyadicErrors.exists_dyadic_below_real hδ
  obtain ⟨p⟩ := certificates m n
  exact ⟨ofRational p hm.le hn.le⟩

end MaxCutGames.Integration.RealTarget

/-!
The value of the actual finite Unique Games instance is its maximum satisfied
constraint fraction. Maximization ranges over every finite vertex labeling;
the denominator counts stored constraint occurrences, including repetitions.
The natural-number maximum totalizes an empty labeling type at zero. The
attainment and threshold equivalences require a positive alphabet.
-/

namespace MaxCutGames.Integration.InstanceValue

open MaxCutGames.Foundations
open Target

/-- The maximum number of satisfied occurrences among all vertex labelings. -/
def maxSatisfied {q : Nat} (g : Instance q) : Nat :=
  Finset.univ.sup (fun labeling : Fin g.vertices → Fin q =>
    countSatisfied labeling g.constraints)

/-- The usual instance value: the largest satisfied fraction of its stored
constraint list. The denominator is positive by the `Instance` invariant. -/
noncomputable def value {q : Nat} (g : Instance q) : ℝ :=
  (maxSatisfied g : ℝ) / g.constraints.length

theorem countSatisfied_le_maxSatisfied {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    countSatisfied labeling g.constraints ≤ maxSatisfied g := by
  unfold maxSatisfied
  exact Finset.le_sup
    (f := fun labeling : Fin g.vertices → Fin q => countSatisfied labeling g.constraints)
    (Finset.mem_univ labeling)

theorem maxSatisfied_le_length {q : Nat} (g : Instance q) :
    maxSatisfied g ≤ g.constraints.length := by
  apply Finset.sup_le
  intro labeling _
  exact countSatisfied_le_length labeling g.constraints

theorem maxSatisfied_attained {q : Nat} (g : Instance q) (hq : 0 < q) :
    ∃ labeling : Fin g.vertices → Fin q,
      countSatisfied labeling g.constraints = maxSatisfied g := by
  have inhabited : (Finset.univ : Finset (Fin g.vertices → Fin q)).Nonempty :=
    ⟨fun _ => ⟨0, hq⟩, Finset.mem_univ _⟩
  obtain ⟨labeling, _, hmax⟩ := Finset.exists_mem_eq_sup Finset.univ inhabited
    (fun labeling : Fin g.vertices → Fin q => countSatisfied labeling g.constraints)
  exact ⟨labeling, hmax.symm⟩

theorem value_attained {q : Nat} (g : Instance q) (hq : 0 < q) :
    ∃ labeling : Fin g.vertices → Fin q,
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length = value g := by
  obtain ⟨labeling, hlabeling⟩ := maxSatisfied_attained g hq
  exact ⟨labeling, by rw [hlabeling]; rfl⟩

theorem labeling_rate_le_value {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤ value g := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast countSatisfied_le_maxSatisfied g labeling
  · exact Nat.cast_nonneg _

/-- This value uses the same rate already defined for the encoded gap target. -/
theorem satisfactionRate_le_value {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    (GapSemantics.satisfactionRate g labeling : ℝ) ≤ value g := by
  simpa [GapSemantics.satisfactionRate] using labeling_rate_le_value g labeling

theorem value_nonneg {q : Nat} (g : Instance q) : 0 ≤ value g :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem value_le_one {q : Nat} (g : Instance q) : value g ≤ 1 := by
  have hlength : (0 : ℝ) < g.constraints.length := by
    exact_mod_cast g.constraintCount_positive
  rw [value, div_le_iff₀ hlength, one_mul]
  exact_mod_cast maxSatisfied_le_length g

theorem value_mem_unitInterval {q : Nat} (g : Instance q) :
    value g ∈ Set.Icc (0 : ℝ) 1 := ⟨value_nonneg g, value_le_one g⟩

/-- Existential real completeness is precisely a lower bound on instance value. -/
theorem exists_rate_ge_iff {q : Nat} (g : Instance q) (hq : 0 < q) (a : ℝ) :
    (∃ labeling : Fin g.vertices → Fin q,
      a ≤ (countSatisfied labeling g.constraints : ℝ) / g.constraints.length) ↔
      a ≤ value g := by
  constructor
  · rintro ⟨labeling, hlabeling⟩
    exact hlabeling.trans (labeling_rate_le_value g labeling)
  · intro hvalue
    obtain ⟨labeling, hlabeling⟩ := value_attained g hq
    exact ⟨labeling, hlabeling.symm ▸ hvalue⟩

/-- Universal real soundness is precisely an upper bound on instance value. -/
theorem forall_rate_le_iff {q : Nat} (g : Instance q) (hq : 0 < q) (b : ℝ) :
    (∀ labeling : Fin g.vertices → Fin q,
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤ b) ↔
      value g ≤ b := by
  constructor
  · intro hall
    obtain ⟨labeling, hlabeling⟩ := value_attained g hq
    exact hlabeling ▸ hall labeling
  · intro hvalue labeling
    exact (labeling_rate_le_value g labeling).trans hvalue

theorem completeAt_iff_value {q : Nat} (e : RationalError) (g : Instance q)
    (hq : 0 < q) :
    CompleteAt e g ↔ 1 - (GapSemantics.errorValue e : ℝ) ≤ value g := by
  rw [GapSemantics.completeAt_iff_real, exists_rate_ge_iff g hq]

theorem soundAt_iff_value {q : Nat} (e : RationalError) (g : Instance q)
    (hq : 0 < q) :
    SoundAt e g ↔ value g ≤ (GapSemantics.errorValue e : ℝ) := by
  rw [GapSemantics.soundAt_iff_real, forall_rate_le_iff g hq]

/-- The unchanged real target certificate gives literal `val(U) ≥ 1 - ε`. -/
theorem realTarget_completeness {ε δ : ℝ}
    (p : RealTarget.PolynomialGapReduction ε δ) (formula : Formula)
    (hformula : formula.Satisfiable) :
    1 - ε ≤ value (p.reduce formula) := by
  have hq : 0 < p.alphabet := lt_of_lt_of_le (by decide : 0 < 2) p.alphabetAtLeastTwo
  exact (exists_rate_ge_iff (p.reduce formula) hq (1 - ε)).mp
    (p.completeness formula hformula)

/-- The unchanged real target certificate gives literal `val(U) ≤ δ`. -/
theorem realTarget_soundness {ε δ : ℝ}
    (p : RealTarget.PolynomialGapReduction ε δ) (formula : Formula)
    (hformula : ¬ formula.Satisfiable) :
    value (p.reduce formula) ≤ δ := by
  have hq : 0 < p.alphabet := lt_of_lt_of_le (by decide : 0 < 2) p.alphabetAtLeastTwo
  exact (forall_rate_le_iff (p.reduce formula) hq δ).mp
    (p.soundness formula hformula)

theorem realTarget_value_guarantees {ε δ : ℝ}
    (p : RealTarget.PolynomialGapReduction ε δ) :
    Nonempty (Turing.TM2ComputableInPolyTime Complexity.formulaEncoding.encode
        (Complexity.gameEncoding p.alphabet).encode p.reduce) ∧
      (∀ formula : Formula, formula.Satisfiable → 1 - ε ≤ value (p.reduce formula)) ∧
      (∀ formula : Formula, ¬ formula.Satisfiable → value (p.reduce formula) ≤ δ) := by
  exact ⟨⟨p.computation⟩, realTarget_completeness p, realTarget_soundness p⟩

end MaxCutGames.Integration.InstanceValue

end OAI
