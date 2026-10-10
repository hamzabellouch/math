import Mathlib

namespace OAI

/-! # Finite measurable codes exhaust the off-diagonal

A countable separating family can be truncated without losing more than an
arbitrarily small part of a finite measure on pairs.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

def finiteSeparationCode (A : ℕ → Set X) (n : ℕ) (x : X) : Fin n → Bool := by
  classical
  exact fun i => if x∈A i then true else false

theorem measurable_finiteSeparationCode {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i))
    (n : ℕ) : Measurable (finiteSeparationCode A n) := by
  classical
  apply Measurable.of_eval
  intro i
  exact measurable_const.piecewise (hA i) measurable_const

def codeSeparatedPairs (A : ℕ → Set X) (n : ℕ) : Set (X×X) :=
  {z | finiteSeparationCode A n z.1≠finiteSeparationCode A n z.2}

theorem measurableSet_codeSeparatedPairs {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i))
    (n : ℕ) : MeasurableSet (codeSeparatedPairs A n) := by
  exact (measurableSet_eq_fun ((measurable_finiteSeparationCode hA n).comp measurable_fst)
    ((measurable_finiteSeparationCode hA n).comp measurable_snd)).compl

omit [MeasurableSpace X] in
theorem monotone_codeSeparatedPairs (A : ℕ → Set X) : Monotone (codeSeparatedPairs A) := by
  classical
  intro n m hnm z hz he
  apply hz
  funext i
  have h := congrFun he (⟨i.val,lt_of_lt_of_le i.isLt hnm⟩ : Fin m)
  simpa only [finiteSeparationCode] using h

omit [MeasurableSpace X] in
theorem iUnion_codeSeparatedPairs {A : ℕ → Set X}
    (hsep : ∀ x y, (∀ i, x∈A i ↔ y∈A i) → x=y) :
    (⋃ n, codeSeparatedPairs A n)={z : X×X | z.1≠z.2} := by
  classical
  ext z
  constructor
  · intro hz he
    obtain ⟨n,hn⟩ := mem_iUnion.mp hz
    exact hn (congrArg (finiteSeparationCode A n) he)
  · intro hz
    by_contra h
    apply hz
    apply hsep
    intro i
    have hi : ¬z∈codeSeparatedPairs A (i+1) := fun hi => h (mem_iUnion.mpr ⟨i+1,hi⟩)
    have he : finiteSeparationCode A (i+1) z.1=finiteSeparationCode A (i+1) z.2 :=
      not_not.mp hi
    have hc := congrFun he (⟨i,Nat.lt_succ_self i⟩ : Fin (i+1))
    have hd := congrArg (fun b : Bool => b=true) hc
    simpa [finiteSeparationCode] using Iff.of_eq hd

theorem tendsto_codeSeparatedPairs_measure (σ : Measure (X×X)) [IsFiniteMeasure σ]
    {A : ℕ → Set X} (hsep : ∀ x y, (∀ i, x∈A i ↔ y∈A i) → x=y) :
    Tendsto (fun n => σ.real (codeSeparatedPairs A n)) atTop
      (𝓝 (σ.real {z : X×X | z.1≠z.2})) := by
  have h := tendsto_measure_iUnion_atTop (μ:=σ) (monotone_codeSeparatedPairs A)
  rw [iUnion_codeSeparatedPairs hsep] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

theorem exists_finite_separation_code [MeasurableSpace.CountablySeparated X]
    (σ : Measure (X×X)) [IsFiniteMeasure σ] {c : ℝ}
    (hc : c<σ.real {z : X×X | z.1≠z.2}) :
    ∃ n : ℕ, ∃ f : X → (Fin n → Bool), Measurable f ∧
      c<σ.real {z : X×X | f z.1≠f z.2} := by
  obtain ⟨A,hA,hsep⟩ := exists_seq_separating (α:=X) MeasurableSet.univ univ
  have hsep' : ∀ x y, (∀ i, x∈A i ↔ y∈A i) → x=y :=
    fun x y h => hsep x (mem_univ _) y (mem_univ _) h
  have h := (tendsto_codeSeparatedPairs_measure σ hsep').eventually (Ioi_mem_nhds hc)
  obtain ⟨n,hn⟩ := h.exists
  exact ⟨n,finiteSeparationCode A n,measurable_finiteSeparationCode hA n,hn⟩

end RegularPointCoordinates

end

end OAI
