import Mathlib

namespace OAI

universe u_S u_T

noncomputable section

namespace Problem310.ConcreteLabels

open MeasureTheory ProbabilityTheory

/-- The actual terminal-bit law used at parameter `p`. -/
def bitLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure Bool :=
  bernoulliMeasure true false ⟨p, hp0, hp1⟩

instance bitLaw_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bitLaw p hp0 hp1) := by
  unfold bitLaw
  infer_instance

@[simp] theorem bitLaw_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bitLaw p hp0 hp1 {true} = ENNReal.ofReal p := by
  simp [bitLaw, unitInterval.toNNReal, ENNReal.ofReal, Real.toNNReal_of_nonneg hp0]
  rfl

@[simp] theorem bitLaw_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bitLaw p hp0 hp1 {false} = ENNReal.ofReal (1 - p) := by
  simp [bitLaw, unitInterval.toNNReal, ENNReal.ofReal,
    Real.toNNReal_of_nonneg (sub_nonneg.mpr hp1)]
  rfl

/-- The actual fair law for selector table entries. -/
def fairLaw : Measure Bool := bitLaw (1 / 2) (by norm_num) (by norm_num)

instance fairLaw_probability : IsProbabilityMeasure fairLaw := by
  unfold fairLaw
  infer_instance

@[simp] theorem fairLaw_singleton (b : Bool) : fairLaw {b} = (2 : ENNReal)⁻¹ := by
  have hh : ENNReal.ofReal ((1 : ℝ) / 2) = (2 : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  cases b <;> norm_num [fairLaw] <;> exact hh

/-- A finite table of independent fair selectors. -/
def selectorLaw (S : Type u_S) [Fintype S] : Measure (S → Bool) :=
  Measure.pi fun _ => fairLaw

instance selectorLaw_probability (S : Type u_S) [Fintype S] :
    IsProbabilityMeasure (selectorLaw S) := by
  unfold selectorLaw
  infer_instance

/-- A finite table of independent Bernoulli terminal entries. -/
def terminalLaw (T : Type u_T) [Fintype T] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Measure (T → Bool) := Measure.pi fun _ => bitLaw p hp0 hp1

instance terminalLaw_probability (T : Type u_T) [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (terminalLaw T p hp0 hp1) := by
  unfold terminalLaw
  infer_instance

/-- Complete finite selector/terminal outcome law, with independent tables. -/
def outcomeLaw (S : Type u_S) (T : Type u_T) [Fintype S] [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure ((S → Bool) × (T → Bool)) :=
  (selectorLaw S).prod (terminalLaw T p hp0 hp1)

instance outcomeLaw_probability (S : Type u_S) (T : Type u_T) [Fintype S] [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (outcomeLaw S T p hp0 hp1) := by
  unfold outcomeLaw
  infer_instance

@[simp] theorem selectorLaw_singleton (S : Type u_S) [Fintype S] (ω : S → Bool) :
    selectorLaw S {ω} = ((2 : ENNReal)⁻¹) ^ Fintype.card S := by
  simp [selectorLaw, Measure.pi_singleton]

theorem selectorLaw_singleton_pos (S : Type u_S) [Fintype S] (ω : S → Bool) :
    0 < selectorLaw S {ω} := by
  rw [selectorLaw_singleton]
  exact ENNReal.pow_pos (by simp) _

/-- Every center-exposure pattern that actually occurs has positive selector mass. -/
theorem selectorLaw_pos_of_nonempty (S : Type u_S) [Fintype S]
    {A : Set (S → Bool)} (hA : A.Nonempty) : 0 < selectorLaw S A := by
  obtain ⟨ω, hω⟩ := hA
  exact (selectorLaw_singleton_pos S ω).trans_le
    (measure_mono (Set.singleton_subset_iff.mpr hω))

@[simp] theorem terminalLaw_singleton (T : Type u_T) [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : T → Bool) :
    terminalLaw T p hp0 hp1 {ω} =
      ∏ t, ENNReal.ofReal (if ω t then p else 1 - p) := by
  rw [terminalLaw, Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro t _
  cases h : ω t <;> simp

theorem terminalLaw_singleton_pos (T : Type u_T) [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 0 < p) (hp' : p < 1)
    (ω : T → Bool) : 0 < terminalLaw T p hp0 hp1 {ω} := by
  rw [terminalLaw_singleton]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro t _
  exact (ENNReal.ofReal_pos.mpr (by split <;> linarith)).ne'

@[simp] theorem outcomeLaw_singleton (S : Type u_S) (T : Type u_T) [Fintype S] [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : (S → Bool) × (T → Bool)) :
    outcomeLaw S T p hp0 hp1 {ω} =
      selectorLaw S {ω.1} * terminalLaw T p hp0 hp1 {ω.2} := by
  cases ω with
  | mk s t =>
    rw [outcomeLaw, ← Set.singleton_prod_singleton, Measure.prod_prod]

theorem outcomeLaw_singleton_pos (S : Type u_S) (T : Type u_T) [Fintype S] [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 0 < p) (hp' : p < 1)
    (ω : (S → Bool) × (T → Bool)) : 0 < outcomeLaw S T p hp0 hp1 {ω} := by
  rw [outcomeLaw_singleton]
  exact ENNReal.mul_pos (selectorLaw_singleton_pos S ω.1).ne'
    (terminalLaw_singleton_pos T p hp0 hp1 hp hp' ω.2).ne'

end Problem310.ConcreteLabels

end

end OAI
