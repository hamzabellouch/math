import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.FiniteSupportWeights

variable {X ι κ : Type*} [MeasurableSpace X]

theorem ae_finite_support [Countable ι] (μ : Measure X) (a : ι → X → ℝ)
    (h : (∑' i, μ {x | a i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, (Function.support (fun i => a i x)).Finite := by
  simpa only [Function.support, Set.mem_ofPred_eq] using
    (ae_finite_setOfPred_mem (μ := μ) (s := fun i => {x | a i x ≠ 0}) h)

theorem ae_all_finite_support [Countable ι] [Countable κ]
    (μ : Measure X) (a : κ → ι → X → ℝ)
    (h : ∀ k, (∑' i, μ {x | a k i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ k, (Function.support (fun i => a k i x)).Finite := by
  exact ae_all_iff.mpr fun k => ae_finite_support μ (a k) (h k)

def integerCore (σ : ℤ → X → X) (s : Set X) : Set X :=
  {x | ∀ n : ℤ, σ n x ∈ s}

theorem ae_mem_integerCore (μ : Measure X) (σ : ℤ → X → X) (s : Set X)
    (hσ : ∀ n, MeasurePreserving (σ n) μ μ) (hs : ∀ᵐ x ∂μ, x ∈ s) :
    ∀ᵐ x ∂μ, x ∈ integerCore σ s := by
  exact ae_all_iff.mpr fun n => (hσ n).quasiMeasurePreserving.ae hs

theorem measurableSet_integerCore (σ : ℤ → X → X) (s : Set X)
    (hσ : ∀ n, Measurable (σ n)) (hs : MeasurableSet s) :
    MeasurableSet (integerCore σ s) := by
  have heq : integerCore σ s = ⋂ n : ℤ, σ n ⁻¹' s := by
    ext x
    simp [integerCore]
  rw [heq]
  exact MeasurableSet.iInter fun n => hs.preimage (hσ n)

omit [MeasurableSpace X] in

theorem integerCore_subset (σ : ℤ → X → X) (s : Set X)
    (hzero : ∀ x, σ 0 x = x) : integerCore σ s ⊆ s := by
  intro x hx
  simpa only [hzero] using hx 0

omit [MeasurableSpace X] in

theorem mem_integerCore_translate_iff (σ : ℤ → X → X) (s : Set X)
    (hadd : ∀ m n x, σ (m + n) x = σ m (σ n x)) (n : ℤ) (x : X) :
    σ n x ∈ integerCore σ s ↔ x ∈ integerCore σ s := by
  constructor
  · intro hx m
    have hm := hx (m - n)
    simpa only [← hadd, sub_add_cancel] using hm
  · intro hx m
    simpa only [← hadd] using hx (m + n)

theorem ae_all_translates_finite_support [Countable ι] [Countable κ]
    (μ : Measure X) (σ : ℤ → X → X) (a : κ → ι → X → ℝ)
    (hσ : ∀ n, MeasurePreserving (σ n) μ μ)
    (h : ∀ k, (∑' i, μ {x | a k i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ n : ℤ, ∀ k,
      (Function.support (fun i => a k i (σ n x))).Finite := by
  exact ae_mem_integerCore μ σ _ hσ (ae_all_finite_support μ a h)

theorem finite_support_mul_cost (c a : ι → ℝ)
    (ha : (Function.support a).Finite) :
    (Function.support (fun i => c i * a i)).Finite := by
  apply ha.subset
  intro i hi
  simp only [Function.mem_support] at hi ⊢
  exact fun h => hi (by simp [h])

theorem summable_mul_cost (c a : ι → ℝ)
    (ha : (Function.support a).Finite) : Summable (fun i => c i * a i) := by
  exact summable_of_hasFiniteSupport (finite_support_mul_cost c a ha)

theorem exp_neg_tsum_mem_Ioc (c a : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i) :
    Real.exp (-(∑' i, c i * a i)) ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact Real.exp_pos _
  · rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (tsum_nonneg fun i => mul_nonneg (hc i) (ha i))

theorem uniform_nonzero_floor_of_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} =
      ENNReal.ofReal t := by
  have hmeas : MeasurableSet {u : ℝ | Int.floor (u + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  rw [Measure.restrict_apply hmeas]
  have hset : {u : ℝ | Int.floor (u + t) ≠ 0} ∩ Set.Ico 0 1 =
      Set.Ico (1 - t) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ne_eq, Int.floor_eq_zero_iff,
      Set.mem_Ico]
    constructor
    · rintro ⟨hn, hu0, hu1⟩
      refine ⟨?_, hu1⟩
      by_contra h
      apply hn
      constructor <;> linarith
    · rintro ⟨hu0, hu1⟩
      refine ⟨?_, ?_, hu1⟩
      · intro h
        linarith [h.2]
      · linarith
  rw [hset, Real.volume_Ico]
  congr 1
  ring

theorem uniform_nonzero_floor_of_nonpos {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 0) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} =
      ENNReal.ofReal (-t) := by
  have hmeas : MeasurableSet {u : ℝ | Int.floor (u + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  rw [Measure.restrict_apply hmeas]
  have hset : {u : ℝ | Int.floor (u + t) ≠ 0} ∩ Set.Ico 0 1 =
      Set.Ico 0 (-t) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ne_eq, Int.floor_eq_zero_iff,
      Set.mem_Ico]
    constructor
    · rintro ⟨hn, hu0, hu1⟩
      refine ⟨hu0, ?_⟩
      by_contra h
      apply hn
      constructor <;> linarith
    · rintro ⟨hu0, hu1⟩
      refine ⟨?_, hu0, ?_⟩
      · intro h
        linarith [h.1]
      · linarith
  rw [hset, Real.volume_Ico, sub_zero]

theorem uniform_nonzero_floor_le (t : ℝ) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} ≤
      ENNReal.ofReal |t| := by
  by_cases ht : |t| ≤ 1
  · have ht' := abs_le.mp ht
    rcases le_total 0 t with hpos | hneg
    · rw [uniform_nonzero_floor_of_nonneg hpos ht'.2, abs_of_nonneg hpos]
    · rw [uniform_nonzero_floor_of_nonpos ht'.1 hneg, abs_of_nonpos hneg]
  · calc
      _ ≤ (volume.restrict (Set.Ico (0 : ℝ) 1)) Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal |t| := ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge ht))

theorem measure_nonzero_floor_le (μ : Measure X) (u : X → ℝ)
    (hu : MeasurePreserving u μ (volume.restrict (Set.Ico (0 : ℝ) 1))) (t : ℝ) :
    μ {x | Int.floor (u x + t) ≠ 0} ≤ ENNReal.ofReal |t| := by
  have hmeas : MeasurableSet {v : ℝ | Int.floor (v + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  change μ (u ⁻¹' {v : ℝ | Int.floor (v + t) ≠ 0}) ≤ _
  rw [hu.measure_preimage hmeas.nullMeasurableSet]
  exact uniform_nonzero_floor_le t

theorem measurableSet_finite_support {R : Type*} [MeasurableSpace R]
    [MeasurableSingletonClass R] [Zero R] [Countable ι]
    (a : ι → X → R) (ha : ∀ i, Measurable (a i)) :
    MeasurableSet {x | (Function.support (fun i => a i x)).Finite} := by
  classical
  have heq : {x | (Function.support (fun i => a i x)).Finite} =
      ⋃ s : Finset ι, ⋂ i : ι, ⋂ (_ : i ∉ s), {x | a i x = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro hx
      refine ⟨hx.toFinset, ?_⟩
      intro i hi
      by_contra hne
      exact hi (hx.mem_toFinset.mpr hne)
    · rintro ⟨s, hs⟩
      apply s.finite_toSet.subset
      intro i hi
      by_contra his
      exact hi (hs i his)
  rw [heq]
  refine MeasurableSet.iUnion fun s => MeasurableSet.iInter fun i =>
    MeasurableSet.iInter fun _ => ?_
  exact (ha i) (measurableSet_singleton 0)

theorem ae_finite_floor_support [Countable ι] (μ : Measure X) (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) (k : ℤ) :
    ∀ᵐ x ∂μ, (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  have hs : Summable (fun i => |(k : ℝ)| * α i) := hα.mul_left _
  have hbound : (∑' i, μ {x | Int.floor (u i x + (k : ℝ) * α i) ≠ 0}) ≤
      ∑' i, ENNReal.ofReal (|(k : ℝ)| * α i) := by
    apply ENNReal.tsum_le_tsum
    intro i
    simpa only [abs_mul, abs_of_nonneg (hα0 i)] using
      measure_nonzero_floor_le μ (u i) (hu i) ((k : ℝ) * α i)
  exact ae_finite_setOfPred_mem (lt_of_le_of_lt hbound hs.tsum_ofReal_lt_top).ne

theorem ae_all_finite_floor_support [Countable ι] (μ : Measure X) (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∀ᵐ x ∂μ, ∀ k : ℤ,
      (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  exact ae_all_iff.mpr fun k => ae_finite_floor_support μ u hu α hα0 hα k

theorem exists_invariant_conull_floor_support [Countable ι]
    (μ : Measure X) (σ : ℤ → X → X)
    (hσ : ∀ n, MeasurePreserving (σ n) μ μ)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ m n x, σ (m + n) x = σ m (σ n x))
    (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∃ s : Set X, MeasurableSet s ∧ (∀ᵐ x ∂μ, x ∈ s) ∧
      (∀ n x, σ n x ∈ s ↔ x ∈ s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  let a : ℤ → ι → X → ℤ := fun k i x => Int.floor (u i x + (k : ℝ) * α i)
  let s₀ : Set X := {x | ∀ k : ℤ, (Function.support (fun i => a k i x)).Finite}
  have hs₀ : MeasurableSet s₀ := by
    have heq : s₀ = ⋂ k : ℤ, {x | (Function.support (fun i => a k i x)).Finite} := by
      ext x
      simp [s₀]
    rw [heq]
    exact MeasurableSet.iInter fun k => measurableSet_finite_support (a k)
      (fun i => ((hu i).measurable.add_const _).floor)
  refine ⟨integerCore σ s₀,
    measurableSet_integerCore σ s₀ (fun n => (hσ n).measurable) hs₀, ?_, ?_, ?_⟩
  · exact ae_mem_integerCore μ σ s₀ hσ (ae_all_finite_floor_support μ u hu α hα0 hα)
  · exact mem_integerCore_translate_iff σ s₀ hadd
  · intro x hx
    exact integerCore_subset σ s₀ hzero hx

end Invariant233.FiniteSupportWeights

end OAI
