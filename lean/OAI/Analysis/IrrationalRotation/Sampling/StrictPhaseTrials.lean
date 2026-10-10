import OAI.Analysis.IrrationalRotation.Model.StrictPhase
import OAI.Analysis.IrrationalRotation.Sampling.StrictPhaseStability
import OAI.Analysis.IrrationalRotation.Sampling.LargePhaseAssembly

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductPhases

theorem strictPhaseGoodCount_ae_eq {ι : Type*} (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] [∀ i, NullSingletonClass (ν i)]
    (J : Finset ι) (b : ℝ) (k : ℤ) (hk : k ≠ 0) :
    ∀ᵐ θ ∂Measure.infinitePi ν, strictPhaseGoodCount J b k θ = phaseGoodCount J b k θ := by
  classical
  have hcoord : ∀ i : ι, ∀ᵐ θ ∂Measure.infinitePi ν,
      (1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Ioo b (1 - b) ↔
        1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc b (1 - b)) := by
    intro i
    have hi : ∀ᵐ x ∂(Measure.infinitePi ν).map (fun θ : ι → ℝ => θ i),
        (1 - Int.fract ((k : ℝ) * x) ∈ Set.Ioo b (1 - b) ↔
          1 - Int.fract ((k : ℝ) * x) ∈ Set.Icc b (1 - b)) := by
      rw [Measure.infinitePi_map_eval]
      exact eventuallyEqSet_iff.mp (threshold_Ioo_ae_eq_Icc (ν i) (by exact_mod_cast hk) b)
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hi
  filter_upwards [(Filter.eventually_all_finset J).mpr (fun i _ => hcoord i)] with θ hθ
  unfold strictPhaseGoodCount phaseGoodCount
  congr 1
  ext i
  simp only [Finset.mem_filter]
  exact and_congr_right fun hi => hθ i hi

theorem strictLargePhaseFailure_ae_eq {ι : Type*} (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] [∀ i, NullSingletonClass (ν i)]
    (J : Finset ι) {N : ℝ} (hN : 0 < N) :
    strictLargePhaseFailure J N =ᵐ[Measure.infinitePi ν] largePhaseFailure J N := by
  let times := largePhaseTimes N ((J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card))
  have hc : ∀ᵐ θ ∂Measure.infinitePi ν, ∀ k ∈ times,
      strictPhaseGoodCount J ((J.card : ℝ) ^ (-19 / 20 : ℝ)) k θ =
        phaseGoodCount J ((J.card : ℝ) ^ (-19 / 20 : ℝ)) k θ := by
    apply (Filter.eventually_all_finset times).mpr
    intro k hk
    apply strictPhaseGoodCount_ae_eq ν J _ k
    intro hzero
    have hh := ((mem_largePhaseTimes hN).mp hk).1
    simp only [hzero, Int.cast_zero, abs_zero] at hh
    linarith
  apply eventuallyEqSet_iff.mpr
  filter_upwards [hc] with θ hθ
  change (∃ k ∈ times, (strictPhaseGoodCount J _ k θ : ℝ) < (J.card : ℝ) / 20) ↔
    (∃ k ∈ times, (phaseGoodCount J _ k θ : ℝ) < (J.card : ℝ) / 20)
  constructor
  · rintro ⟨k, hk, hsmall⟩
    exact ⟨k, hk, by simpa only [hθ k hk] using hsmall⟩
  · rintro ⟨k, hk, hsmall⟩
    exact ⟨k, hk, by simpa only [hθ k hk] using hsmall⟩

theorem not_mem_strictLargePhaseFailure_iff {ι : Type*} (J : Finset ι)
    {N : ℝ} (hN : 0 < N) (θ : ι → ℝ) :
    θ ∉ strictLargePhaseFailure J N ↔ strictLargePhaseCondition J N θ := by
  simp only [strictLargePhaseFailure, Set.mem_ofPred_eq, not_exists, not_and,
    not_lt, strictLargePhaseCondition, mem_largePhaseTimes hN]
  constructor
  · intro h k hlo hhi
    exact h k ⟨hlo, hhi⟩
  · intro h k hk
    exact h k hk.1 hk.2

theorem uniformProduct_measure_strictLargePhaseFailure_le {ι : Type*}
    (S : ι → ℝ) (hS : ∀ i, 0 < S i) (J : Finset ι)
    {N : ℝ} (hN : 0 < N) (hm : 100 ≤ (J.card : ℝ))
    (hblock : ∀ i ∈ J, S i = N) :
    (Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Set.Icc (1 / S i) (2 / S i)))) (strictLargePhaseFailure J N) ≤
      ENNReal.ofReal (failureBound J.card) := by
  let ν : ι → Measure ℝ := fun i =>
    ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))
  let (i : ι) : IsProbabilityMeasure (ν i) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) (hS i))
  let (i : ι) : NullSingletonClass (ν i) :=
    InvariantProjection.IndependentAngles.intervalLaw_nullSingletonClass _ _
  change (Measure.infinitePi ν) (strictLargePhaseFailure J N) ≤ _
  rw [measure_congr (strictLargePhaseFailure_ae_eq ν J hN)]
  apply measure_largePhaseFailure_le (Measure.infinitePi ν) J N hm
  · exact fun k => iIndepSet_phaseMiss_infinitePi ν _ k
  · intro k hk i hi
    rw [infinitePi_phaseMiss_eq ν _ k i]
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top (ν i) _) (by positivity)).mpr
    change (ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))).real
      {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉
        Set.Icc ((J.card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - (J.card : ℝ) ^ (-19 / 20 : ℝ))} ≤ _
    rw [hblock i hi]
    exact Invariant233.ModuloIntervalMeasure.uniform_angle_threshold_miss_le
      hN ((mem_largePhaseTimes hN).mp hk).1 (by positivity)

theorem intervalProduct_ae_strict_bounds {ι : Type*} [Countable ι]
    (S : ι → ℝ) (hS : ∀ i, 0 < S i) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
        (Set.Icc (1 / S i) (2 / S i))),
      ∀ i, θ i ∈ Set.Ioo (1 / S i) (2 / S i) := by
  let ν : ι → Measure ℝ := fun i =>
    ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))
  let (i : ι) : IsProbabilityMeasure (ν i) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) (hS i))
  let (i : ι) : NullSingletonClass (ν i) :=
    InvariantProjection.IndependentAngles.intervalLaw_nullSingletonClass _ _
  apply ae_all_iff.mpr
  intro i
  have hi : ∀ᵐ x ∂ν i, x ∈ Set.Ioo (1 / S i) (2 / S i) := by
    have hc : ∀ᵐ x ∂ν i, x ∈ Set.Icc (1 / S i) (2 / S i) :=
      ae_cond_mem measurableSet_Icc
    filter_upwards [hc, (ν i).ae_ne (1 / S i), (ν i).ae_ne (2 / S i)] with x hx hlo hhi
    exact ⟨lt_of_le_of_ne hx.1 hlo.symm, lt_of_le_of_ne hx.2 hhi⟩
  have hmap : ∀ᵐ x ∂(Measure.infinitePi ν).map (fun θ : ι → ℝ => θ i),
      x ∈ Set.Ioo (1 / S i) (2 / S i) := by
    rw [Measure.infinitePi_map_eval]
    exact hi
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hmap

theorem exists_strict_phase_block (m : ℕ) {N : ℝ} (hN : 0 < N)
    (hm : 100 ≤ (m : ℝ)) (hB : failureBound m < 1) :
    ∃ θ : Fin m → ℝ,
      (∀ i, θ i ∈ Set.Ioo (1 / N) (2 / N)) ∧
      strictLargePhaseCondition Finset.univ N θ := by
  let ν : Fin m → Measure ℝ := fun _ =>
    ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))
  let : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) hN)
  let μ := Measure.infinitePi ν
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hbad : μ (strictLargePhaseFailure (Finset.univ : Finset (Fin m)) N) < 1 := by
    have hh := uniformProduct_measure_strictLargePhaseFailure_le
      (fun _ : Fin m => N) (fun _ => hN) Finset.univ hN
      (by simpa only [Finset.card_univ, Fintype.card_fin] using hm) (fun _ _ => rfl)
    apply hh.trans_lt
    simpa only [Finset.card_univ, Fintype.card_fin] using ENNReal.ofReal_lt_one.mpr hB
  have hbox := intervalProduct_ae_strict_bounds (fun _ : Fin m => N) (fun _ => hN)
  by_contra hnone
  have hnone' : ∀ θ : Fin m → ℝ, (∀ i, θ i ∈ Set.Ioo (1 / N) (2 / N)) →
      ¬ strictLargePhaseCondition Finset.univ N θ := by
    simpa only [not_exists, not_and] using hnone
  have hbadAE : ∀ᵐ θ ∂μ, θ ∈ strictLargePhaseFailure Finset.univ N := by
    filter_upwards [hbox] with θ hθ
    by_contra hn
    exact hnone' θ hθ ((not_mem_strictLargePhaseFailure_iff Finset.univ hN θ).mp hn)
  have hmass : μ (strictLargePhaseFailure Finset.univ N) = 1 := by
    calc
      μ (strictLargePhaseFailure Finset.univ N) = μ Set.univ := by
        apply measure_congr
        apply eventuallyEqSet_iff.mpr
        filter_upwards [hbadAE] with θ hθ
        exact iff_of_true hθ (Set.mem_univ θ)
      _ = 1 := measure_univ
  rw [hmass] at hbad
  exact (lt_irrefl (1 : ℝ≥0∞)) hbad

theorem eventually_strictLargePhaseCondition {ι : Type*} (J : Finset ι)
    (hJ : 0 < J.card) {N : ℝ} (hN : 0 < N) (θ : ι → ℝ)
    (hθ : strictLargePhaseCondition J N θ) :
    ∀ᶠ φ in 𝓝 θ, strictLargePhaseCondition J N φ := by
  classical
  let b : ℝ := (J.card : ℝ) ^ (-19 / 20 : ℝ)
  let times := largePhaseTimes N ((J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card))
  let witness : ℤ → Finset ι := fun k =>
    J.filter (fun i => 1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Ioo b (1 - b))
  have hb : 0 < b := Real.rpow_pos_of_pos (by exact_mod_cast hJ) _
  have htests := eventually_finite_phase_tests times witness θ hb
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  filter_upwards [htests] with φ hφ
  intro k hlo hhi
  have hk : k ∈ times := (mem_largePhaseTimes hN).mpr ⟨hlo, hhi⟩
  have hc : (J.card : ℝ) / 20 ≤ ((witness k).card : ℝ) := hθ k hlo hhi
  have hsub : witness k ⊆ J.filter
      (fun i => 1 - Int.fract ((k : ℝ) * φ i) ∈ Set.Ioo b (1 - b)) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, hφ k hk i hi⟩
  apply hc.trans
  change ((witness k).card : ℝ) ≤ ((J.filter
    (fun i => 1 - Int.fract ((k : ℝ) * φ i) ∈ Set.Ioo b (1 - b))).card : ℝ)
  exact_mod_cast Finset.card_le_card hsub

theorem isOpen_strictLargePhaseCondition {ι : Type*} (J : Finset ι)
    (hJ : 0 < J.card) {N : ℝ} (hN : 0 < N) :
    IsOpen {θ : ι → ℝ | strictLargePhaseCondition J N θ} := by
  apply isOpen_iff_mem_nhds.mpr
  intro θ hθ
  exact eventually_strictLargePhaseCondition J hJ hN θ hθ

theorem eventually_exists_strict_phase_block :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℝ, 0 < N →
      ∃ θ : Fin m → ℝ, (∀ i, θ i ∈ Set.Ioo (1 / N) (2 / N)) ∧
        strictLargePhaseCondition Finset.univ N θ := by
  have hb : ∀ᶠ m : ℕ in atTop, failureBound m ≤ Real.exp (-(m : ℝ)) :=
    tendsto_natCast_atTop_atTop.eventually eventually_failureBound_le_exp
  filter_upwards [hb, eventually_ge_atTop (100 : ℕ)] with m hbound hm
  intro N hN
  apply exists_strict_phase_block m hN (by exact_mod_cast hm)
  apply hbound.trans_lt
  apply Real.exp_lt_one_iff.mpr
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 100) hm)
  linarith

end Invariant233.ProductPhases

end OAI
