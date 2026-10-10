import OAI.Analysis.CircleDomains.Probability.FusionSmallSets
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace OAI

/-! Countable and atomless tests control integration against any finite measure
whose point masses have square norm at most one. This supplies the test-measure
step in finite law splitting; the atomless remainder is the restriction away
from the actual positive point masses. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def positiveAtoms (ν : Measure X) : Set X := {x | 0 < ν {x}}

omit [SecondCountableTopology X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem countable_positiveAtoms (ν : Measure X) [SFinite ν] : (positiveAtoms ν).Countable := by
  simpa [positiveAtoms] using
    (Measure.countable_meas_level_set_pos (μ := ν) (g := id) measurable_id)

omit [SecondCountableTopology X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem nullSingleton_restrict_compl_positiveAtoms (ν : Measure X) :
    NullSingletonClass (ν.restrict (positiveAtoms ν)ᶜ) := by
  constructor
  intro x
  by_cases hx : x ∈ positiveAtoms ν
  · rw [Measure.restrict_apply (measurableSet_singleton x)]
    simp [hx]
  · have hzero : ν {x} = 0 := le_antisymm (not_lt.mp hx) bot_le
    exact le_antisymm ((Measure.restrict_le_self {x}).trans hzero.le) bot_le

def HasAtomicSquareBound (ν : Measure X) : Prop :=
  ∀ F : Finset X, ∑ x ∈ F, (ν {x}).toReal ^ 2 ≤ 1

omit [BorelSpace C(PathTime, X)] in
theorem PassesHitTests.lintegral_le_of_atomic_square_bound
    {ν : Measure X} [IsFiniteMeasure ν] {μ : ProbabilityMeasure C(PathTime, X)}
    {C : ℝ} (hC : 0 ≤ C) (hν : HasAtomicSquareBound ν)
    (htest : PassesHitTests C μ (positiveAtoms ν) (ν.restrict (positiveAtoms ν)ᶜ)) :
    ∫⁻ x, pathHitProbability μ x ∂ν ≤ ENNReal.ofReal C := by
  classical
  let D := positiveAtoms ν
  have hD : D.Countable := countable_positiveAtoms ν
  rw [← lintegral_add_compl _ hD.measurableSet, htest.2, add_zero,
    lintegral_countable _ hD, ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  have hF : (↑(F.image (fun x : D => (x : X))) : Set X) ⊆ D := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have heq (a : X → ℝ) :
      ∑ x ∈ F.image (fun x : D => (x : X)), a x = ∑ x ∈ F, a x.val :=
    Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)
  have hp : (∑ x ∈ F, pathHitReal μ x.val ^ 2) ≤ C ^ 2 := by
    simpa only [heq] using htest.1 _ hF
  have ha : (∑ x ∈ F, (ν {x.val}).toReal ^ 2) ≤ 1 := by
    simpa only [heq] using hν (F.image (fun x : D => (x : X)))
  have hpr : Real.sqrt (∑ x ∈ F, pathHitReal μ x.val ^ 2) ≤ C :=
    Real.sqrt_le_iff.mpr ⟨hC, hp⟩
  have har : Real.sqrt (∑ x ∈ F, (ν {x.val}).toReal ^ 2) ≤ 1 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using ha⟩
  have hsum : (∑ x ∈ F, pathHitReal μ x.val * (ν {x.val}).toReal) ≤ C := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt F
      (fun x : D => pathHitReal μ x.val) (fun x : D => (ν {x.val}).toReal)
    exact hcs.trans ((mul_le_mul hpr har (Real.sqrt_nonneg _) hC).trans_eq (mul_one C))
  calc
    ∑ x ∈ F, pathHitProbability μ x.val * ν {x.val} =
        ENNReal.ofReal (∑ x ∈ F, pathHitReal μ x.val * (ν {x.val}).toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
        mul_nonneg (pathHitReal_nonneg _ _) ENNReal.toReal_nonneg)]
      apply Finset.sum_congr rfl
      intro x _
      rw [ENNReal.ofReal_mul (pathHitReal_nonneg _ _)]
      rw [pathHitReal, ENNReal.ofReal_toReal (ne_of_lt
        (lt_of_le_of_lt (pathHitProbability_le_one _ _) (by simp))),
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hsum

theorem exists_test_law_for_atomic_measure
    {Z : Type*} (law : Z → ProbabilityMeasure C(PathTime, X))
    {A : Set Z} {C : ℝ} (hC : 0 ≤ C) (hA : ¬HitTestSmall law C A)
    (ν : Measure X) [IsFiniteMeasure ν] (hν : HasAtomicSquareBound ν) :
    ∃ z ∈ A, ∫ x, pathHitReal (law z) x ∂ν ≤ C := by
  classical
  have hnull := nullSingleton_restrict_compl_positiveAtoms ν
  obtain ⟨z, hz, htest⟩ : ∃ z ∈ A,
      PassesHitTests C (law z) (positiveAtoms ν) (ν.restrict (positiveAtoms ν)ᶜ) := by
    by_contra h
    apply hA
    refine ⟨positiveAtoms ν, countable_positiveAtoms ν,
      ν.restrict (positiveAtoms ν)ᶜ, inferInstance, hnull, ?_⟩
    intro z hz hpass
    exact h ⟨z, hz, hpass⟩
  have hi := htest.lintegral_le_of_atomic_square_bound hC hν
  have he := integral_toReal (μ := ν) (measurable_pathHitProbability_point (law z)).aemeasurable
    (Eventually.of_forall fun x => lt_of_le_of_lt
      (pathHitProbability_le_one (law z) x) (by simp))
  refine ⟨z, hz, ?_⟩
  change (∫ x, (pathHitProbability (law z) x).toReal ∂ν) ≤ C
  rw [he]
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hi

end CircleDomainRigidity

end

end OAI
