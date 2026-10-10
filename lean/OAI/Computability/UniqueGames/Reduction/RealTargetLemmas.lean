import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Model
import OAI.Computability.UniqueGames.Reduction.BinaryLinear
import OAI.Computability.UniqueGames.Reduction.GapSemanticsLemmas

namespace OAI

section

/-! The arbitrary-real-error target and its exact passage from encoded rational
gap reductions. The same formula map and actual machine certificate are reused;
choosing smaller error tolerances does not change the computation. -/

namespace UniqueGamesTheorem.Integration.RealTarget

open UniqueGamesTheorem.Foundations
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

end UniqueGamesTheorem.Integration.RealTarget

end

section

/-!
The value of the actual finite Unique Games instance is its maximum satisfied
constraint fraction. Maximization ranges over every finite vertex labeling;
the denominator counts stored constraint occurrences, including repetitions.
The natural-number maximum totalizes an empty labeling type at zero. The
attainment and threshold equivalences require a positive alphabet.
-/

namespace UniqueGamesTheorem.Integration.InstanceValue

open UniqueGamesTheorem.Foundations
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

end UniqueGamesTheorem.Integration.InstanceValue

end

section

namespace UniqueGamesTheorem.Integration.TranslationTarget

open UniqueGamesTheorem.Foundations
open Target

/-- The full output form asserted in Theorem 1.1, including both real gaps,
the actual polynomial-time machine, and one fixed binary alphabet. -/
structure PolynomialGapReduction (ε δ : ℝ) extends RealTarget.PolynomialGapReduction ε δ where
  dimension : Nat
  coordinates : Fin alphabet ≃ BinaryLinear.Vector dimension
  translations : ∀ formula : Formula,
    IsTranslationInstance coordinates (reduce formula)

def ofRational {e d : RationalError} {ε δ : ℝ}
    (p : Complexity.PolynomialGapReduction e d) (s : Nat)
    (coordinates : Fin p.alphabet ≃ BinaryLinear.Vector s)
    (translations : ∀ formula, IsTranslationInstance coordinates (p.reduce formula))
    (hε : (GapSemantics.errorValue e : ℝ) ≤ ε)
    (hδ : (GapSemantics.errorValue d : ℝ) ≤ δ) : PolynomialGapReduction ε δ where
  toPolynomialGapReduction := RealTarget.ofRational p hε hδ
  dimension := s
  coordinates := coordinates
  translations := translations

/-- Full dyadic certificates suffice for all positive real tolerances, retaining
the exact same translation coordinates and actual program in each instance. -/
theorem for_all_real_of_dyadic
    (certificates : ∀ m n : Nat,
      ∃ p : Complexity.PolynomialGapReduction
        (DyadicErrors.dyadicError m) (DyadicErrors.dyadicError n),
      ∃ s : Nat, ∃ coordinates : Fin p.alphabet ≃ BinaryLinear.Vector s,
        ∀ formula, IsTranslationInstance coordinates (p.reduce formula))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    Nonempty (PolynomialGapReduction ε δ) := by
  obtain ⟨m, hm⟩ := DyadicErrors.exists_dyadic_below_real hε
  obtain ⟨n, hn⟩ := DyadicErrors.exists_dyadic_below_real hδ
  obtain ⟨p, s, coordinates, translations⟩ := certificates m n
  exact ⟨ofRational p s coordinates translations hm.le hn.le⟩

end UniqueGamesTheorem.Integration.TranslationTarget

end

section

/-! Injective vertex addresses may leave unused output vertices. The actual
instance is obtained by mapping endpoints in the original constraint list;
constraint order, multiplicity, and permutation tables are retained exactly. -/

namespace UniqueGamesTheorem.Integration.VertexEmbedding

open UniqueGamesTheorem.Foundations.Target
open GapSemantics TranslationTarget

def embedConstraint {n m q : Nat} (f : Fin n → Fin m) (c : Constraint n q) :
    Constraint m q where
  source := f c.source
  target := f c.target
  permutation := c.permutation

@[simp] theorem embedConstraint_satisfied {n m q : Nat} (f : Fin n → Fin m)
    (c : Constraint n q) (labeling : Fin m → Fin q) :
    (embedConstraint f c).satisfied labeling = c.satisfied (labeling ∘ f) := rfl

@[simp] theorem embedConstraint_permutation {n m q : Nat} (f : Fin n → Fin m)
    (c : Constraint n q) : (embedConstraint f c).permutation = c.permutation := rfl

theorem count_map {n m q : Nat} (f : Fin n → Fin m)
    (constraints : List (Constraint n q)) (labeling : Fin m → Fin q) :
    countSatisfied labeling (constraints.map (embedConstraint f)) =
      countSatisfied (labeling ∘ f) constraints := by
  induction constraints with
  | nil => rfl
  | cons c cs ih =>
      by_cases hc : c.satisfied (labeling ∘ f) = true <;> simp [countSatisfied, ih, hc]

def embedInstance {q m : Nat} (g : Instance q) (f : Fin g.vertices → Fin m)
    (_hf : Function.Injective f) : Instance q where
  vertices := m
  constraints := g.constraints.map (embedConstraint f)
  nonempty h := g.nonempty (List.map_eq_nil_iff.mp h)

@[simp] theorem embedInstance_vertices {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    (embedInstance g f hf).vertices = m := rfl

theorem embedInstance_constraints {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    (embedInstance g f hf).constraints = g.constraints.map (embedConstraint f) := rfl

@[simp] theorem embedInstance_length {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    (embedInstance g f hf).constraints.length = g.constraints.length := List.length_map _

theorem count_embed {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f)
    (labeling : Fin m → Fin q) :
    countSatisfied labeling (embedInstance g f hf).constraints =
      countSatisfied (labeling ∘ f) g.constraints := count_map f g.constraints labeling

theorem satisfactionRate_embed {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f)
    (labeling : Fin m → Fin q) :
    satisfactionRate (embedInstance g f hf) labeling =
      satisfactionRate g (labeling ∘ f) := by
  unfold satisfactionRate
  simp only [embedInstance, count_map, List.length_map]

/-- The extension is only used as a semantic witness, not by the instance constructor. -/
noncomputable def extendLabeling {n m q : Nat} (f : Fin n → Fin m)
    (labeling : Fin n → Fin q) (defaultLabel : Fin q) (v : Fin m) : Fin q := by
  classical
  exact if h : ∃ u, f u = v then labeling (Classical.choose h) else defaultLabel

@[simp] theorem extendLabeling_apply {n m q : Nat} (f : Fin n → Fin m)
    (hf : Function.Injective f) (labeling : Fin n → Fin q)
    (defaultLabel : Fin q) (v : Fin n) :
    extendLabeling f labeling defaultLabel (f v) = labeling v := by
  classical
  have hx : ∃ u, f u = f v := ⟨v, rfl⟩
  rw [extendLabeling, dite_eq_left hx]
  exact congrArg labeling (hf (Classical.choose_spec hx))

theorem extendLabeling_comp {n m q : Nat} (f : Fin n → Fin m)
    (hf : Function.Injective f) (labeling : Fin n → Fin q) (defaultLabel : Fin q) :
    extendLabeling f labeling defaultLabel ∘ f = labeling := by
  funext v
  exact extendLabeling_apply f hf labeling defaultLabel v

theorem soundAt_embed {q m : Nat} (error : RationalError) (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f)
    (hg : SoundAt error g) : SoundAt error (embedInstance g f hf) := by
  intro labeling
  change (Fin m → Fin q) at labeling
  simp only [embedInstance, count_map, List.length_map]
  exact hg (labeling ∘ f)

theorem completeAt_embed {q m : Nat} (error : RationalError) (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) (hq : 0 < q)
    (hg : CompleteAt error g) : CompleteAt error (embedInstance g f hf) := by
  obtain ⟨labeling, hl⟩ := hg
  refine ⟨extendLabeling f labeling ⟨0, hq⟩, ?_⟩
  simp only [embedInstance, count_map, List.length_map, extendLabeling_comp f hf]
  exact hl

theorem completeAt_embed_iff {q m : Nat} (error : RationalError) (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) (hq : 0 < q) :
    CompleteAt error (embedInstance g f hf) ↔ CompleteAt error g := by
  constructor
  · rintro ⟨labeling, hl⟩
    change (Fin m → Fin q) at labeling
    refine ⟨labeling ∘ f, ?_⟩
    simpa only [embedInstance, count_map, List.length_map] using hl
  · exact completeAt_embed error g f hf hq

theorem soundAt_embed_iff {q m : Nat} (error : RationalError) (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) (hq : 0 < q) :
    SoundAt error (embedInstance g f hf) ↔ SoundAt error g := by
  constructor
  · intro hg labeling
    have hl := hg (extendLabeling f labeling ⟨0, hq⟩)
    simpa only [embedInstance, count_map, List.length_map, extendLabeling_comp f hf] using hl
  · exact soundAt_embed error g f hf

theorem isTranslationInstance_embed_iff {q s m : Nat}
    (coordinates : Fin q ≃ BinaryLinear.Vector s) (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    IsTranslationInstance coordinates (embedInstance g f hf) ↔
      IsTranslationInstance coordinates g := by
  constructor
  · intro hg c hc
    exact hg (embedConstraint f c) (List.mem_map.mpr ⟨c, hc, rfl⟩)
  · intro hg c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact hg d hd

end UniqueGamesTheorem.Integration.VertexEmbedding

end

section

namespace UniqueGamesTheorem.Reduction.ActualHomogeneous

open Integration.BinaryLinear
open scoped BigOperators

abbrev E (k : Nat) := F2 × (Fin k → F2 × F2)
abbrev Ambient (k : Nat) := F2 × (Fin k → Fin 3 → F2)

variable {dimension : Nat}

def tau : E dimension →ₗ[F2] F2 := LinearMap.fst F2 _ _
def hBasis (k : Nat) : E k := (1, 0)
def firstBasis (j : Fin dimension) : E dimension := (0, Pi.single j (1, 0))
def secondBasis (j : Fin dimension) : E dimension := (0, Pi.single j (0, 1))
def coordinateBasis (j : Fin dimension) (i : Fin 2) : E dimension :=
  if i = 0 then firstBasis j else secondBasis j

@[simp] theorem tau_hBasis : tau (hBasis dimension) = 1 := rfl
@[simp] theorem tau_firstBasis (j : Fin dimension) : tau (firstBasis j) = 0 := rfl
@[simp] theorem tau_secondBasis (j : Fin dimension) : tau (secondBasis j) = 0 := rfl

theorem pair_fst_ite (p : Prop) [Decidable p] (a b : F2 × F2) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split_ifs <;> rfl
theorem pair_snd_ite (p : Prop) [Decidable p] (a b : F2 × F2) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split_ifs <;> rfl

theorem coordinate_decomposition (x : E dimension) :
    x = x.1 • hBasis dimension + ∑ j : Fin dimension,
      ((x.2 j).1 • firstBasis j + (x.2 j).2 • secondBasis j) := by
  apply Prod.ext
  · simp [hBasis, firstBasis, secondBasis, Prod.fst_sum]
  · funext j
    apply Prod.ext <;>
      simp [hBasis, firstBasis, secondBasis, Pi.single_apply,
        Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, pair_fst_ite, pair_snd_ite]

theorem linearMap_expansion {R : Type*} [AddCommGroup R] [Module F2 R]
    (X : E dimension →ₗ[F2] R) (x : E dimension) :
    X x = x.1 • X (hBasis dimension) + ∑ j : Fin dimension,
      ((x.2 j).1 • X (firstBasis j) + (x.2 j).2 • X (secondBasis j)) := by
  conv_lhs => rw [coordinate_decomposition x]
  simp

def homogeneous (b : Fin dimension → F2) : Submodule F2 (Ambient dimension) where
  carrier := {x | ∀ j, x.2 j 0 + x.2 j 1 + x.2 j 2 = b j * x.1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j
    change (x.2 j 0 + y.2 j 0) + (x.2 j 1 + y.2 j 1) +
      (x.2 j 2 + y.2 j 2) = b j * (x.1 + y.1)
    calc
      _ = (x.2 j 0 + x.2 j 1 + x.2 j 2) +
          (y.2 j 0 + y.2 j 1 + y.2 j 2) := by ring
      _ = b j * x.1 + b j * y.1 := by rw [hx j, hy j]
      _ = _ := by ring
  smul_mem' := by
    intro c x hx j
    change c * x.2 j 0 + c * x.2 j 1 + c * x.2 j 2 = b j * (c * x.1)
    calc
      _ = c * (x.2 j 0 + x.2 j 1 + x.2 j 2) := by ring
      _ = c * (b j * x.1) := by rw [hx j]
      _ = _ := by ring

def embed (b : Fin dimension → F2) : E dimension →ₗ[F2] Ambient dimension where
  toFun x := (x.1, fun j => ![(x.2 j).1, (x.2 j).2,
    b j * x.1 + (x.2 j).1 + (x.2 j).2])
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext j i
      fin_cases i <;> simp
      ring
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · funext j i
      fin_cases i <;> simp [smul_eq_mul]
      ring

theorem embed_mem (b : Fin dimension → F2) (x : E dimension) :
    embed b x ∈ homogeneous b := by
  intro j
  change (x.2 j).1 + (x.2 j).2 + (b j * x.1 + (x.2 j).1 + (x.2 j).2) = b j * x.1
  have h1 := CharTwo.add_self_eq_zero ((x.2 j).1)
  have h2 := CharTwo.add_self_eq_zero ((x.2 j).2)
  calc
    _ = b j * x.1 + (((x.2 j).1 + (x.2 j).1) + ((x.2 j).2 + (x.2 j).2)) := by ring
    _ = _ := by rw [h1, h2]; simp

def equivalence (b : Fin dimension → F2) : E dimension ≃ₗ[F2] homogeneous b where
  toFun x := ⟨embed b x, embed_mem b x⟩
  invFun x := (x.1.1, fun j => (x.1.2 j 0, x.1.2 j 1))
  left_inv x := by rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j i
      fin_cases i
      · rfl
      · rfl
      · change b j * x.1.1 + x.1.2 j 0 + x.1.2 j 1 = x.1.2 j 2
        rw [← x.property j]
        have h1 := CharTwo.add_self_eq_zero (x.1.2 j 0)
        have h2 := CharTwo.add_self_eq_zero (x.1.2 j 1)
        calc
          _ = x.1.2 j 2 + ((x.1.2 j 0 + x.1.2 j 0) + (x.1.2 j 1 + x.1.2 j 1)) := by ring
          _ = _ := by rw [h1, h2]; simp
  map_add' x y := Subtype.ext ((embed b).map_add x y)
  map_smul' c x := Subtype.ext ((embed b).map_smul c x)

theorem finrank_E (k : Nat) : Module.finrank F2 (E k) = 1 + 2 * k := by
  simp [E, Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm]

theorem finrank_homogeneous (b : Fin dimension → F2) :
    Module.finrank F2 (homogeneous b) = 1 + 2 * dimension := by
  rw [← (equivalence b).finrank_eq, finrank_E]

end UniqueGamesTheorem.Reduction.ActualHomogeneous

end

end OAI
