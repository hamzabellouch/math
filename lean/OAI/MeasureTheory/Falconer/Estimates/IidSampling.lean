import OAI.MeasureTheory.Falconer.Estimates.SamplingTail
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

/-!
# Independent sampling of direction and point labels

The finite product law below samples the original labels, before their
geometric coordinates are taken. Repeated coordinates therefore retain
their original incidence fibers, as required by `ang:planar-measures`.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators

noncomputable def iidLaw {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) (n : ℕ) : Measure (Fin n → X) :=
  Measure.pi (fun _ => (ν : Measure X))

instance {X : Type*} [MeasurableSpace X] (ν : ProbabilityMeasure X) (n : ℕ) :
    IsProbabilityMeasure (iidLaw ν n) := by
  unfold iidLaw
  infer_instance

noncomputable def iidCount {X : Type*} (A : Set X) {n : ℕ} (ω : Fin n → X) : ℝ :=
  ∑ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (ω i)

theorem measurable_iidCount {X : Type*} [MeasurableSpace X] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) : Measurable (iidCount A (n := n)) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.indicator hA).comp (measurable_pi_apply i)

private theorem iid_cell_mass {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) (n : ℕ) (i : Fin n) (A : Set X) (hA : MeasurableSet A) :
    (iidLaw ν n).real {ω | ω i ∈ A} = (ν : Measure X).real A := by
  have hmass : iidLaw ν n {ω | ω i ∈ A} = (ν : Measure X) A := by
    calc
      iidLaw ν n {ω | ω i ∈ A} =
          ((iidLaw ν n).map (Function.eval i)) A :=
        (Measure.map_apply (measurable_pi_apply i) hA).symm
      _ = (ν : Measure X) A := by
        simpa only [iidLaw] using congrArg (fun μ : Measure X => μ A)
          (measurePreserving_eval (fun _ : Fin n => (ν : Measure X)) i).map_eq
  exact congrArg ENNReal.toReal hmass

private theorem iid_indicators_independent {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) (n : ℕ) (A : Set X) (hA : MeasurableSet A) :
    iIndepFun (fun i : Fin n => {ω : Fin n → X | ω i ∈ A}.indicator
      (fun _ => (1 : ℝ))) (iidLaw ν n) := by
  have h := iIndepFun_pi (μ := fun _ : Fin n => (ν : Measure X))
    (X := fun _ : Fin n => A.indicator (fun _ => (1 : ℝ)))
    (fun _ => (measurable_const.indicator hA).aemeasurable)
  have heq : (fun (i : Fin n) (ω : Fin n → X) =>
      {ω : Fin n → X | ω i ∈ A}.indicator (fun _ => (1 : ℝ)) ω) =
      (fun (i : Fin n) (ω : Fin n → X) => A.indicator (fun _ => (1 : ℝ)) (ω i)) := by
    funext i ω
    by_cases hω : ω i ∈ A <;> simp [hω]
  rw [heq]
  exact h

/-- Counts are simultaneously controlled on every prescribed measurable
cell, with an exponentially small failure probability. -/
theorem iid_finite_cells_tail {X κ : Type*} [MeasurableSpace X] [DecidableEq κ]
    (ν : ProbabilityMeasure X) (n : ℕ) (B : Finset κ) (A : κ → Set X)
    (hA : ∀ j, MeasurableSet (A j)) (p T : κ → ℝ) (L : ℝ)
    (hp : ∀ j ∈ B, 0 ≤ p j)
    (hprob : ∀ j ∈ B, (ν : Measure X).real (A j) ≤ p j)
    (hT : ∀ j ∈ B, (n : ℝ) * (exp 1 - 1) * p j + L ≤ T j) :
    iidLaw ν n (⋃ j ∈ B, {ω | T j ≤ iidCount (A j) ω}) ≤
      ENNReal.ofReal ((B.card : ℝ) * exp (-L)) := by
  classical
  have h := finite_sample_count_failure (iidLaw ν n) B (Finset.univ : Finset (Fin n))
    (fun j i => {ω : Fin n → X | ω i ∈ A j})
    (fun j i => (hA j).preimage (measurable_pi_apply i))
    (fun j _ => iid_indicators_independent ν n (A j) (hA j)) p T L hp
    (fun j hj i _ => (iid_cell_mass ν n i (A j) (hA j)).trans_le (hprob j hj))
    (by simpa using hT)
  have heq : ∀ j (ω : Fin n → X),
      (∑ i : Fin n, {ω : Fin n → X | ω i ∈ A j}.indicator (fun _ => (1 : ℝ)) ω) =
      iidCount (A j) ω := by
    intro j ω
    apply Finset.sum_congr rfl
    intro i _
    by_cases hω : ω i ∈ A j <;> simp [hω]
  simpa only [heq] using h

noncomputable def iidAverage {X : Type*} (f : X → ℝ) {n : ℕ} (ω : Fin n → X) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, f (ω i)

theorem integrable_iidAverage {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) {f : X → ℝ} (hf : Integrable f (ν : Measure X)) (n : ℕ) :
    Integrable (iidAverage f (n := n)) (iidLaw ν n) := by
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  exact integrable_comp_eval hf

theorem integral_iidAverage {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) {f : X → ℝ} (hf : Integrable f (ν : Measure X))
    {n : ℕ} (hn : 0 < n) :
    (∫ ω, iidAverage f ω ∂iidLaw ν n) = ∫ x, f x ∂(ν : Measure X) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heval (i : Fin n) : (∫ ω, f (ω i) ∂iidLaw ν n) = ∫ x, f x ∂(ν : Measure X) := by
    exact integral_comp_eval (μ := fun _ : Fin n => (ν : Measure X)) hf.aestronglyMeasurable
  simp only [iidAverage]
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [heval]
    simp [hnR]
  · intro i _
    exact integrable_comp_eval hf

theorem iidAverage_le_one {X : Type*} (f : X → ℝ) (hf : ∀ x, f x ≤ 1)
    {n : ℕ} (hn : 0 < n) (ω : Fin n → X) : iidAverage f ω ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold iidAverage
  calc
    (n : ℝ)⁻¹ * ∑ i : Fin n, f (ω i) ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun _ _ => hf _)) (inv_nonneg.mpr hnR.le)
    _ = 1 := by simp [hnR.ne']

/-- Simultaneous cell bounds and at least half the expected incidence can
be achieved by one sample of the original labels. -/
theorem exists_iid_sample_with_counts_and_incidence {X κ : Type*}
    [MeasurableSpace X] [DecidableEq κ] (ν : ProbabilityMeasure X)
    {n : ℕ} (hn : 0 < n) (B : Finset κ) (A : κ → Set X)
    (hA : ∀ j, MeasurableSet (A j)) (p T : κ → ℝ) (L : ℝ)
    (hp : ∀ j ∈ B, 0 ≤ p j)
    (hprob : ∀ j ∈ B, (ν : Measure X).real (A j) ≤ p j)
    (hT : ∀ j ∈ B, (n : ℝ) * (exp 1 - 1) * p j + L ≤ T j)
    (f : X → ℝ) (hf : Integrable f (ν : Measure X)) (hf1 : ∀ x, f x ≤ 1)
    {I : ℝ} (hI : 0 < I) (hmean : I ≤ ∫ x, f x ∂(ν : Measure X))
    (hsmall : (B.card : ℝ) * exp (-L) ≤ I / 4) :
    ∃ ω : Fin n → X,
      (∀ j ∈ B, iidCount (A j) ω < T j) ∧ I / 2 ≤ iidAverage f ω := by
  classical
  let Bad : Set (Fin n → X) := ⋃ j ∈ B, {ω | T j ≤ iidCount (A j) ω}
  have hBad : MeasurableSet Bad := MeasurableSet.biUnion B.countable_toSet fun j _ =>
    measurableSet_le measurable_const (measurable_iidCount (hA j) n)
  have hmass : (iidLaw ν n).real Bad ≤ I / 4 := by
    have h := (iid_finite_cells_tail ν n B A hA p T L hp hprob hT).trans
      (ENNReal.ofReal_le_ofReal hsmall)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [Bad, measureReal_def,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ I / 4)] using hr
  obtain ⟨ω, hω, hinc⟩ := exists_good_sample_incidence (iidLaw ν n) (iidAverage f)
    (integrable_iidAverage ν hf n) (iidAverage_le_one f hf1 hn) Bad hBad hI
    (by simpa only [integral_iidAverage ν hf hn] using hmean) hmass
  refine ⟨ω, ?_, hinc⟩
  intro j hj
  apply lt_of_not_ge
  intro hbad
  exact hω (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hbad⟩⟩)

/-- For cell masses at most `K * s`, only the additive term `L` in the
sampling constant is needed to pay for simultaneous control, provided
the expected scale count `n * s` is at least one. -/
theorem exists_iid_sample_scale_counts {X κ : Type*}
    [MeasurableSpace X] [DecidableEq κ] (ν : ProbabilityMeasure X)
    {n : ℕ} (hn : 0 < n) (B : Finset κ) (A : κ → Set X)
    (hA : ∀ j, MeasurableSet (A j)) (s : κ → ℝ) {K L : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hscale : ∀ j ∈ B, 1 ≤ (n : ℝ) * s j)
    (hprob : ∀ j ∈ B, (ν : Measure X).real (A j) ≤ K * s j)
    (f : X → ℝ) (hf : Integrable f (ν : Measure X)) (hf1 : ∀ x, f x ≤ 1)
    {I : ℝ} (hI : 0 < I) (hmean : I ≤ ∫ x, f x ∂(ν : Measure X))
    (hsmall : (B.card : ℝ) * exp (-L) ≤ I / 4) :
    ∃ ω : Fin n → X,
      (∀ j ∈ B, iidCount (A j) ω < ((exp 1 - 1) * K + L) * (n : ℝ) * s j) ∧
      I / 2 ≤ iidAverage f ω := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply exists_iid_sample_with_counts_and_incidence ν hn B A hA (fun j => K * s j)
    (fun j => ((exp 1 - 1) * K + L) * (n : ℝ) * s j) L _ hprob _ f hf hf1 hI hmean hsmall
  · intro j hj
    have hs : 0 ≤ s j := by nlinarith [hscale j hj]
    exact mul_nonneg hK hs
  · intro j hj
    have hLs := mul_le_mul_of_nonneg_left (hscale j hj) hL
    nlinarith

end Falconer

end OAI
