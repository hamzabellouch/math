import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233

theorem fin_pi_absolutelyContinuous {n : ℕ} {X : Fin n → Type*}
    [∀ i, MeasurableSpace (X i)] (μ ν : (i : Fin n) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i, μ i ≪ ν i) : Measure.pi μ ≪ Measure.pi ν := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | succ n ih =>
    have ht : Measure.pi (fun i : Fin n => μ (Fin.succAbove 0 i)) ≪
        Measure.pi (fun i : Fin n => ν (Fin.succAbove 0 i)) :=
      ih (fun i => μ (Fin.succAbove 0 i)) (fun i => ν (Fin.succAbove 0 i))
        (fun i => h (Fin.succAbove 0 i))
    have hp := (h 0).prod ht
    have hm := (measurePreserving_piFinSuccAbove μ 0).symm
    have hn := (measurePreserving_piFinSuccAbove ν 0).symm
    have hx := hp.map (MeasurableEquiv.piFinSuccAbove X 0).symm.measurable
    rwa [hm.map_eq, hn.map_eq] at hx

theorem fintype_pi_absolutelyContinuous {I : Type*} [Fintype I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ ν : (i : I) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i, μ i ≪ ν i) : Measure.pi μ ≪ Measure.pi ν := by
  let e := (Fintype.equivFin I).symm
  have ha := fin_pi_absolutelyContinuous (fun i => μ (e i)) (fun i => ν (e i))
    (fun i => h (e i))
  have hmap := ha.map (MeasurableEquiv.piCongrLeft X e).measurable
  rwa [(measurePreserving_piCongrLeft μ e).map_eq,
    (measurePreserving_piCongrLeft ν e).map_eq] at hmap

theorem pi_finite_sum {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : I) → J → Measure (X i)) [∀ i j, IsFiniteMeasure (μ i j)] :
    Measure.pi (fun i => ∑ j, μ i j) =
      ∑ pattern : I → J, Measure.pi (fun i => μ i (pattern i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  simp_rw [Measure.finsetSum_apply, Measure.pi_pi]
  exact (Fintype.prod_sum (fun i j => μ i j (s i))).symm

theorem pi_add_eq_sum_bool {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ ν : (i : I) → Measure (X i))
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)] :
    Measure.pi (fun i => μ i + ν i) =
      ∑ pattern : I → Bool, Measure.pi (fun i => if pattern i then ν i else μ i) := by
  have : ∀ i (b : Bool), IsFiniteMeasure (if b then ν i else μ i) := by
    intro i b
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> infer_instance
  simpa only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, add_comm] using
    pi_finite_sum (fun i (b : Bool) => if b then ν i else μ i)

end Invariant233

end

end OAI
