import OAI.Analysis.IrrationalRotation.Sampling.StrictPhaseTrials

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductPhases

theorem infinitePi_ae_nonresonant {ι : Type*} [Countable ι]
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, NullSingletonClass (ν i)] :
    ∀ᵐ θ ∂Measure.infinitePi ν, ∀ i, ∀ k : ℤ, k ≠ 0 →
      Int.fract ((k : ℝ) * θ i) ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro k
  by_cases hk : k = 0
  · exact Filter.Eventually.of_forall (fun _ h => (h hk).elim)
  have hi : ∀ᵐ x ∂ν i, Int.fract ((k : ℝ) * x) ≠ 0 := by
    filter_upwards [ae_threshold_ne (ν i) (k := (k : ℝ)) (by exact_mod_cast hk) 1] with x hx
    intro hz
    exact hx (by simp only [hz, sub_zero])
  have hmap : ∀ᵐ x ∂(Measure.infinitePi ν).map (fun θ : ι → ℝ => θ i),
      Int.fract ((k : ℝ) * x) ≠ 0 := by
    rw [Measure.infinitePi_map_eval]
    exact hi
  exact (ae_of_ae_map (measurable_pi_apply i).aemeasurable hmap).mono (fun _ h _ => h)

theorem exists_ae_requirement_outside_bad {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {bad : Set Ω} {P : Ω → Prop}
    (hbad : μ bad < 1) (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧ x ∉ bad := by
  by_contra hnone
  have hbadAE : ∀ᵐ x ∂μ, x ∈ bad := by
    filter_upwards [hP] with x hx
    by_contra hnot
    exact hnone ⟨x, hx, hnot⟩
  have hmass : μ bad = 1 := by
    calc
      μ bad = μ Set.univ := by
        apply measure_congr
        apply eventuallyEqSet_iff.mpr
        filter_upwards [hbadAE] with x hx
        exact iff_of_true hx (Set.mem_univ x)
      _ = 1 := measure_univ
  rw [hmass] at hbad
  exact (lt_irrefl (1 : ℝ≥0∞)) hbad

theorem exists_nonresonant_strict_phase_block (m : ℕ) {N : ℝ} (hN : 0 < N)
    (hm : 100 ≤ (m : ℝ)) (hB : failureBound m < 1) :
    ∃ θ : Fin m → ℝ,
      (∀ i, θ i ∈ Set.Ioo (1 / N) (2 / N)) ∧
      (∀ i, ∀ k : ℤ, k ≠ 0 → Int.fract ((k : ℝ) * θ i) ≠ 0) ∧
      strictLargePhaseCondition Finset.univ N θ := by
  let ν : Fin m → Measure ℝ := fun _ =>
    ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))
  let : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) hN)
  let : NullSingletonClass
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_nullSingletonClass _ _
  have hbad : (Measure.infinitePi ν)
      (strictLargePhaseFailure (Finset.univ : Finset (Fin m)) N) < 1 := by
    have hh := uniformProduct_measure_strictLargePhaseFailure_le
      (fun _ : Fin m => N) (fun _ => hN) Finset.univ hN
      (by simpa only [Finset.card_univ, Fintype.card_fin] using hm) (fun _ _ => rfl)
    apply hh.trans_lt
    simpa only [Finset.card_univ, Fintype.card_fin] using ENNReal.ofReal_lt_one.mpr hB
  have hP := (intervalProduct_ae_strict_bounds (fun _ : Fin m => N) (fun _ => hN)).and
    (infinitePi_ae_nonresonant ν)
  obtain ⟨θ, hθ, hgood⟩ := exists_ae_requirement_outside_bad (Measure.infinitePi ν) hbad hP
  exact ⟨θ, hθ.1, hθ.2, (not_mem_strictLargePhaseFailure_iff Finset.univ hN θ).mp hgood⟩

theorem eventually_exists_nonresonant_strict_phase_block :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℝ, 0 < N →
      ∃ θ : Fin m → ℝ, (∀ i, θ i ∈ Set.Ioo (1 / N) (2 / N)) ∧
        (∀ i, ∀ k : ℤ, k ≠ 0 → Int.fract ((k : ℝ) * θ i) ≠ 0) ∧
        strictLargePhaseCondition Finset.univ N θ := by
  have hb : ∀ᶠ m : ℕ in atTop, failureBound m ≤ Real.exp (-(m : ℝ)) :=
    tendsto_natCast_atTop_atTop.eventually eventually_failureBound_le_exp
  filter_upwards [hb, eventually_ge_atTop (100 : ℕ)] with m hbound hm
  intro N hN
  apply exists_nonresonant_strict_phase_block m hN (by exact_mod_cast hm)
  apply hbound.trans_lt
  apply Real.exp_lt_one_iff.mpr
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 100) hm)
  linarith

end Invariant233.ProductPhases

end OAI
