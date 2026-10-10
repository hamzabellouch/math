import OAI.Analysis.CircleDomains.Transfer.ResidualImage
import OAI.Analysis.CircleDomains.Selection.ResidualVisits

namespace OAI

/-! The rational-interval residual constraints in the allowed path definition
are Borel. The incidence side uses the actual prior law or level measure;
the toll side retains parameter multiplicity after each finite deletion. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

abbrev RationalPathTime := {q : ℚ // q ∈ Icc (0 : ℚ) 1}

def RationalPathTime.toTime (q : RationalPathTime) : PathTime :=
  ⟨(q.val : ℝ), by
    constructor
    · exact_mod_cast q.property.1
    · exact_mod_cast q.property.2⟩

def deletedWeight {X : Type*} (P : Set X) (m : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  if x ∈ P then 0 else m x

theorem countable_support_deletedWeight {X : Type*} (P : Set X) {m : X → ℝ≥0∞}
    (hm : (Function.support m).Countable) :
    (Function.support (deletedWeight P m)).Countable := by
  apply hm.mono
  intro x hx
  simp only [Function.mem_support, deletedWeight] at hx ⊢
  by_contra h
  simp only [h, ite_self] at hx
  exact hx rfl

variable {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def ResidualIncidenceBound (B : Set X) (I : Set PathTime) (R : Set (Y × X))
    (P : Set X) (ν : Measure Y) (m : X → ℝ≥0∞) (Γ : TaggedPath X) : Prop :=
  ν {y | (Γ, y) ∈ residualIncidence B I R P} ≤
    residualToll B I (deletedWeight P m) Γ

theorem measurableSet_residualIncidenceBound {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) {R : Set (Y × X)} (hR : IsClosed R)
    {P : Set X} (hP : P.Finite) (ν : Measure Y) [SFinite ν]
    {m : X → ℝ≥0∞} (hm : (Function.support m).Countable) :
    MeasurableSet {Γ | ResidualIncidenceBound B I R P ν m Γ} :=
  measurableSet_le (measurable_residualIncidenceMass hB hI hR hP ν)
    (measurable_residualToll hB hI (countable_support_deletedWeight P hm))

def ResidualConstraintFamily (B : Set X) (R : ℕ → Set (Y × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Y) (m : ℕ → X → ℝ≥0∞)
    (Γ : TaggedPath X) : Prop :=
  ∀ i n (a b : RationalPathTime),
    ResidualIncidenceBound B (Icc a.toTime b.toTime) (R i) (P i n) (ν i) (m i) Γ

theorem measurableSet_residualConstraintFamily {B : Set X} (hB : IsClosed B)
    {R : ℕ → Set (Y × X)} (hR : ∀ i, IsClosed (R i))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Y) [∀ i, SFinite (ν i)]
    {m : ℕ → X → ℝ≥0∞} (hm : ∀ i, (Function.support (m i)).Countable) :
    MeasurableSet {Γ | ResidualConstraintFamily B R P ν m Γ} := by
  simp only [ResidualConstraintFamily, ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_residualIncidenceBound hB isClosed_Icc (hR i) (P i n).finite_toSet
        (ν i) (hm i)

end CircleDomainRigidity

end

end OAI
