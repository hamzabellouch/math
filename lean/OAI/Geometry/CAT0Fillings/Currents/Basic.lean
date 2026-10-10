import Mathlib
import OAI.Geometry.CAT0Fillings.Model

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]

namespace BoundedLip
omit [MeasurableSpace X] in
lemma continuous {b : X → ℝ} (hb : BoundedLip b) : Continuous b :=
  hb.1.choose_spec.continuous

omit [MeasurableSpace X] in
lemma const (a : ℝ) : BoundedLip (fun _ : X => a) := by
  exact ⟨⟨0, LipschitzWith.const a⟩, |a|, fun _ => le_rfl⟩

omit [MeasurableSpace X] in
lemma add {b c : X → ℝ} (hb : BoundedLip b) (hc : BoundedLip c) :
    BoundedLip (fun x => b x + c x) := by
  obtain ⟨⟨Kb, hKb⟩, Mb, hMb⟩ := hb
  obtain ⟨⟨Kc, hKc⟩, Mc, hMc⟩ := hc
  refine ⟨⟨Kb + Kc, hKb.add hKc⟩, Mb + Mc, ?_⟩
  intro x
  exact (abs_add_le _ _).trans (add_le_add (hMb x) (hMc x))

omit [MeasurableSpace X] in
lemma const_mul (a : ℝ) {b : X → ℝ} (hb : BoundedLip b) :
    BoundedLip (fun x => a * b x) := by
  obtain ⟨⟨K, hK⟩, M, hM⟩ := hb
  refine ⟨⟨⟨|a|, abs_nonneg a⟩ * K, ?_⟩, |a| * M, ?_⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    change dist (a * b x) (a * b y) ≤ (|a| * (K : ℝ)) * dist x y
    rw [Real.dist_eq, ← mul_sub, abs_mul]
    calc |a| * |b x - b y| ≤ |a| * ((K : ℝ) * dist x y) :=
           mul_le_mul_of_nonneg_left (hK.dist_le_mul x y) (abs_nonneg a)
         _ = _ := by ring
  · intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg a)
end BoundedLip

lemma isMetricCurrent_zero (k : ℕ) : IsMetricCurrent (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) where
  offDomain := by intros; rfl
  linearFirst := by intros; simp
  linearCoord := by intros; simp
  sequentialContinuity := by intros; exact tendsto_const_nhds
  locality := by intros; rfl
  finiteMass := by
    refine ⟨0, inferInstance, ?_⟩
    intro b π hb hπ
    simp

lemma mass_nonneg {k : ℕ} (T : Functional X k) : 0 ≤ mass T := by
  apply Real.sInf_nonneg
  rintro r ⟨μ, _, _, rfl⟩
  exact ENNReal.toReal_nonneg

lemma mass_le_measure {k : ℕ} {T : Functional X k} {μ : Measure X}
    (hμ : IsFiniteMeasure μ) (hT : Controls T μ) : mass T ≤ μ.real univ := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨ν, _, _, rfl⟩
    exact ENNReal.toReal_nonneg
  · exact ⟨μ, hμ, hT, rfl⟩

@[simp] lemma mass_zero (k : ℕ) : mass (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) = 0 := by
  apply le_antisymm
  · have h : Controls (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) (0 : Measure X) := by
      intro b π hb hπ
      simp
    simpa using mass_le_measure (μ := (0 : Measure X)) inferInstance h
  · exact mass_nonneg _

omit [MeasurableSpace X] in
@[simp] lemma boundarySucc_zero (k : ℕ) :
    boundarySucc (fun (_ : X → ℝ) (_ : Fin (k+1) → X → ℝ) => 0) = fun _ _ => 0 := by
  funext b π
  simp [boundarySucc]

omit [MeasurableSpace X] in
@[simp] lemma boundary_zero (k : ℕ) :
    boundary (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) = fun _ _ => 0 := by
  cases k with
  | zero => rfl
  | succ k => exact boundarySucc_zero k

noncomputable def emptyChart (k : ℕ) : IntegerChart X k where
  domain := ∅
  borel := MeasurableSet.empty
  bounded := Bornology.isBounded_empty
  param := fun z => False.elim z.property
  bilipschitz := by
    refine ⟨0, 0, ?_, ?_⟩
    · apply lipschitzWith_iff_dist_le_mul.mpr
      intro a b
      exact False.elim a.property
    · intro a b
      exact False.elim a.property
  multiplicity := fun _ => 0
  integrable := by simp

omit [MeasurableSpace X] in
@[simp] lemma emptyChart_image (k : ℕ) : (emptyChart (X := X) k).image = ∅ := by
  ext x
  simp [IntegerChart.image, emptyChart]

omit [MeasurableSpace X] in
@[simp] lemma emptyChart_action (k : ℕ) :
    (emptyChart (X := X) k).action = fun _ _ => 0 := by
  funext b π
  simp [IntegerChart.action, emptyChart]

lemma integerRectifiable_zero (k : ℕ) :
    IntegerRectifiable (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) := by
  refine ⟨fun _ => emptyChart k, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simp
  · intro i
    rw [emptyChart_action]
    exact isMetricCurrent_zero k
  · simp only [emptyChart_action, mass_zero]
    exact summable_zero
  · intro b π
    simp

lemma isIntegral_zero (k : ℕ) :
    IsIntegral k (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) := by
  cases k with
  | zero => exact ⟨isMetricCurrent_zero 0, integerRectifiable_zero 0⟩
  | succ k =>
    refine ⟨isMetricCurrent_zero _, integerRectifiable_zero _, ?_, ?_⟩
    · rw [boundarySucc_zero]
      exact isMetricCurrent_zero k
    · rw [boundarySucc_zero]
      exact integerRectifiable_zero k

omit [MeasurableSpace X] in
lemma compactlySupported_zero (k : ℕ) :
    CompactlySupported (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) :=
  ⟨∅, isCompact_empty, fun _ _ _ _ => rfl⟩

omit [MeasurableSpace X] in
lemma isCycle_zero (k : ℕ) : IsCycle (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) :=
  boundary_zero k

end Foundations
end CAT0Fillings
end

end OAI
