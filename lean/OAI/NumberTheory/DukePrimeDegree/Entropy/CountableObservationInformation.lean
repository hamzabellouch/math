import OAI.NumberTheory.DukePrimeDegree.Entropy.ObservationInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.HeightObservationEntropy

namespace OAI

/-! # Finite clipping of a countable observation

At a sampled point, clipping above its observed value leaves its atom
unchanged. Positive atom mass also gives a common information bound.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma heightClip_atom_eq_of_lt {Y : Type*} (Q : Y → ℕ) (y : Y)
    {N : ℕ} (hN : Q y < N) :
    {z | heightClip Q N z = heightClip Q N y} = {z | Q z = Q y} := by
  ext z
  simp only [mem_ofPred_eq, heightClip, Fin.mk.injEq]
  omega

lemma observationInformation_heightClip_eventually {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (Q : Y → ℕ) (y : Y) :
    ∀ᶠ N : ℕ in atTop,
      observationInformation ν (heightClip Q N) y = observationInformation ν Q y := by
  filter_upwards [eventually_gt_atTop (Q y)] with N hN
  unfold observationInformation
  rw [heightClip_atom_eq_of_lt Q y hN]

lemma observationInformation_heightClip_le {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (Q : Y → ℕ) (y : Y)
    (hpos : 0 < ν {z | Q z = Q y}) (N : ℕ) :
    observationInformation ν (heightClip Q N) y ≤ observationInformation ν Q y := by
  have hsub : {z | Q z = Q y} ⊆ {z | heightClip Q N z = heightClip Q N y} := by
    intro z hz
    exact congrArg (fun a => (⟨min a N, Nat.lt_succ_of_le (min_le_right a N)⟩ : Fin (N+1))) hz
  have hreal : 0 < ν.real {z | Q z = Q y} :=
    ENNReal.toReal_pos hpos.ne' (measure_ne_top ν _)
  exact neg_le_neg (Real.log_le_log hreal (measureReal_mono hsub))

/-- Integrable countable information is recovered by its finite clips,
without requiring finite Shannon entropy of the countable observation. -/
theorem integral_kernel_heightClip_information_tendsto
    {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    (κ : Kernel S V) [IsMarkovKernel κ]
    (Q : S × V → ℕ) (hQ : Measurable Q)
    (hpos : ∀ᵐ z ∂ρ, 0 < κ z.1 {v | Q (z.1,v) = Q z})
    (hint : Integrable
      (fun z => observationInformation (κ z.1) (fun v => Q (z.1,v)) z.2) ρ) :
    Tendsto (fun N => ∫ z,
      observationInformation (κ z.1) (fun v => heightClip Q N (z.1,v)) z.2 ∂ρ)
      atTop (𝓝 (∫ z, observationInformation (κ z.1) (fun v => Q (z.1,v)) z.2 ∂ρ)) := by
  let I := fun z : S × V => observationInformation (κ z.1) (fun v => Q (z.1,v)) z.2
  apply tendsto_integral_of_dominated_convergence I
  · intro N
    exact (measurable_kernel_observationInformation κ (heightClip Q N)
      (fun a => (heightClip_measurable hQ N) (measurableSet_singleton a))).aestronglyMeasurable
  · exact hint
  · intro N
    filter_upwards [hpos] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (observationInformation_nonneg _ _ _)]
    exact observationInformation_heightClip_le (κ z.1) (fun v => Q (z.1,v)) z.2 hz N
  · apply ae_of_all
    intro z
    apply tendsto_const_nhds.congr'
    filter_upwards [observationInformation_heightClip_eventually
      (κ z.1) (fun v => Q (z.1,v)) z.2] with N hN
    exact hN.symm

end DukePrimeDegree

end

end OAI
