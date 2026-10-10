import OAI.Probability.FreeIsing.Brownian.ArrayObservation
import OAI.Probability.FreeIsing.Stochastic.FiniteIsingBrownianEnergy

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.FiniteIsingFiltering

local instance finiteIsingFilteringNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

abbrev State (d : ℕ) (Ω : Type*) :=
  (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)

def signal (sigma : TreeVertex d → IsingSpin) (i : TreeVertex d) : ℝ :=
  spinSign (sigma i)

lemma measurable_signal : Measurable (signal (d := d)) := by
  apply Measurable.of_eval
  intro i
  have hs : Measurable spinSign := by intro s hs; trivial
  exact hs.comp (measurable_pi_apply i)

def observationFiltration
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hmB : ∀ i t, Measurable (B i t)) (D : Finset (TreeVertex d)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (State d Ω)) :=
  arrayNaturalFiltration (fun i : D => plantedArrayObservation B signal i)
    (fun i t => plantedArrayObservation_measurable hmB measurable_signal i t)

lemma observationFiltration_le_signal
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hmB : ∀ i t, Measurable (B i t)) (D : Finset (TreeVertex d)) :
    observationFiltration B hmB D ≤ signalArrayFiltration B hmB := by
  apply arrayNaturalFiltration_le
  intro i t
  exact (arrayNaturalFiltration_stronglyAdapted (plantedArrayObservation B signal)
    (plantedArrayObservation_measurable hmB measurable_signal) i t).mono
      (arrayObservationFiltration_le_signalArrayFiltration B hmB signal measurable_signal t)

lemma observationFiltration_eq_comap
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hmB : ∀ i t, Measurable (B i t)) (D : Finset (TreeVertex d)) (t : ℝ≥0) :
    observationFiltration B hmB D t = MeasurableSpace.comap
      (fun p : State d Ω => fun i : D => fun s : Set.Iic t =>
        (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i)) inferInstance := by
  rw [observationFiltration, arrayNaturalFiltration_eq_comap]
  congr 1
  ext p i s
  simp only [plantedArrayObservation, signal, add_comm]

abbrev mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) : ℝ :=
  finiteIsingBrownianMean beta D v B (t : ℝ) p

abbrev covariance (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) : ℝ :=
  finiteIsingBrownianCovariance beta D v u B (t : ℝ) p

omit [MeasurableSpace Ω] in
lemma mean_eq_fieldMean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) :
    mean beta D v B t p = FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))
      (fun i : D => plantedArrayObservation B signal i t p) := by
  unfold mean finiteIsingBrownianMean
  congr 1
  ext i
  simp only [finiteIsingBrownianObservation, Real.toNNReal_coe,
    plantedArrayObservation, signal, add_comm]

omit [MeasurableSpace Ω] in
lemma covariance_eq_fieldCovariance (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) :
    covariance beta D v u B t p = FinitePosterior.fieldCovariance (finiteIsingEnergy beta D)
      (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v))
      (fun i : D => plantedArrayObservation B signal i t p) u := by
  unfold covariance finiteIsingBrownianCovariance
  congr 1
  ext i
  simp only [finiteIsingBrownianObservation, Real.toNNReal_coe,
    plantedArrayObservation, signal, add_comm]

omit [MeasurableSpace Ω] in
lemma abs_mean_le_one (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) :
    |mean beta D v B t p| ≤ 1 := by
  rw [mean_eq_fieldMean]
  apply FinitePosterior.abs_fieldMean_le
  intro eta
  cases eta v <;> simp [spinSign]

omit [MeasurableSpace Ω] in
lemma abs_covariance_le_two (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) :
    |covariance beta D v u B t p| ≤ 2 := by
  rw [covariance_eq_fieldCovariance]
  apply (FinitePosterior.abs_fieldCovariance_le _ _ _ _ _ 1 ?_ ?_).trans_eq
    (by norm_num)
  · intro eta
    cases eta u <;> simp [spinSign]
  · intro eta
    cases eta v <;> simp [spinSign]

lemma stronglyAdapted_mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t)) :
    StronglyAdapted (observationFiltration B hmB D) (mean beta D v B) := by
  intro t
  have hobs : StronglyMeasurable[observationFiltration B hmB D t]
      (fun p : State d Ω => fun i : D => plantedArrayObservation B signal i t p) := by
    apply Measurable.stronglyMeasurable
    refine @Measurable.of_eval (State d Ω) D (fun _ => ℝ)
      (observationFiltration B hmB D t) (fun _ => inferInstance) _ ?_
    intro i
    exact (arrayNaturalFiltration_stronglyAdapted
      (fun j : D => plantedArrayObservation B signal j)
      (fun j r => plantedArrayObservation_measurable hmB measurable_signal j r) i t).measurable
  have h := (FinitePosterior.continuous_fieldMean (finiteIsingEnergy beta D)
    (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))).comp_stronglyMeasurable hobs
  change StronglyMeasurable[observationFiltration B hmB D t]
    (fun p => mean beta D v B t p)
  simp_rw [mean_eq_fieldMean]
  exact h

lemma stronglyAdapted_covariance (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t)) :
    StronglyAdapted (observationFiltration B hmB D) (covariance beta D v u B) := by
  intro t
  have hobs : StronglyMeasurable[observationFiltration B hmB D t]
      (fun p : State d Ω => fun i : D => plantedArrayObservation B signal i t p) := by
    apply Measurable.stronglyMeasurable
    refine @Measurable.of_eval (State d Ω) D (fun _ => ℝ)
      (observationFiltration B hmB D t) (fun _ => inferInstance) _ ?_
    intro i
    exact (arrayNaturalFiltration_stronglyAdapted
      (fun j : D => plantedArrayObservation B signal j)
      (fun j r => plantedArrayObservation_measurable hmB measurable_signal j r) i t).measurable
  have h := (FinitePosterior.continuous_fieldCovariance (finiteIsingEnergy beta D)
    (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v)) u).comp_stronglyMeasurable hobs
  change StronglyMeasurable[observationFiltration B hmB D t]
    (fun p => covariance beta D v u B t p)
  simp_rw [covariance_eq_fieldCovariance]
  exact h

omit [MeasurableSpace Ω] in
lemma continuous_mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (p : State d Ω) :
    Continuous (fun t => mean beta D v B t p) := by
  simp only [mean_eq_fieldMean]
  apply (FinitePosterior.continuous_fieldMean _ _ _).comp
  apply continuous_pi
  intro i
  exact (hcB i (p.2 i)).add (NNReal.continuous_coe.mul continuous_const)

omit [MeasurableSpace Ω] in
lemma continuous_covariance (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (p : State d Ω) :
    Continuous (fun t => covariance beta D v u B t p) := by
  simp only [covariance_eq_fieldCovariance]
  apply (FinitePosterior.continuous_fieldCovariance _ _ _ _).comp
  apply continuous_pi
  intro i
  exact (hcB i (p.2 i)).add (NNReal.continuous_coe.mul continuous_const)

lemma progressive_mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    IsStronglyProgressive (observationFiltration B hmB D) (mean beta D v B) :=
  (stronglyAdapted_mean beta D v B hmB).isStronglyProgressive_of_continuous
    (continuous_mean beta D v B hcB)

lemma progressive_covariance (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    IsStronglyProgressive (observationFiltration B hmB D) (covariance beta D v u B) :=
  (stronglyAdapted_covariance beta D v u B hmB).isStronglyProgressive_of_continuous
    (continuous_covariance beta D v u B hcB)

lemma memLp_mean (P : Measure (State d Ω)) [IsFiniteMeasure P]
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (t : ℝ≥0) (p : ℝ≥0∞) : MemLp (mean beta D v B t) p P := by
  apply MemLp.of_bound
    (((stronglyAdapted_mean beta D v B hmB t).mono
      ((observationFiltration B hmB D).le t)).aestronglyMeasurable) 1
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using abs_mean_le_one beta D v B t x

lemma memLp_covariance (P : Measure (State d Ω)) [IsFiniteMeasure P]
    (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (t : ℝ≥0) (p : ℝ≥0∞) : MemLp (covariance beta D v u B t) p P := by
  apply MemLp.of_bound
    (((stronglyAdapted_covariance beta D v u B hmB t).mono
      ((observationFiltration B hmB D).le t)).aestronglyMeasurable) 2
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using abs_covariance_le_two beta D v u B t x

end Problem367.FiniteIsingFiltering

end

end OAI
