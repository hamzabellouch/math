import OAI.Probability.FreeIsing.Spins.ObservationLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance statisticTiltMeasurableSingletonSpin : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩
local instance statisticTiltNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem condDistrib_eq_map_cond_fiber
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSingletonClass A] {μ : Measure Ω} [IsFiniteMeasure μ]
    {S : Ω → A} {Y : Ω → B} (hS : Measurable S) (hY : Measurable Y)
    (a : A) (ha : μ (S ⁻¹' {a}) ≠ 0) :
    condDistrib Y S μ a = (μ[|S ⁻¹' {a}]).map Y := by
  ext s hs
  have hmass : μ.map S {a} ≠ 0 := by
    rwa [Measure.map_apply hS (measurableSet_singleton a)]
  rw [condDistrib_apply_of_ne_zero hS hY a hmass,
    Measure.map_apply hS (measurableSet_singleton a),
    Measure.map_apply (hS.prodMk hY) ((measurableSet_singleton a).prod hs),
    Measure.map_apply hY hs, ProbabilityTheory.cond, Measure.smul_apply,
    Measure.restrict_apply (hY hs)]
  simp only [smul_eq_mul]
  congr 1
  apply congrArg μ
  ext ω
  simp [and_comm]

theorem condExp_spin_statistic_of_linear_posterior
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {S : Ω → IsingSpin}
    {q : Ω → ℝ} {theta : ℝ} (hm : m ≤ mΩ)
    (hq : Measurable[m] q) (hqi : Integrable q μ)
    (hPost : μ[fun ω => spinSign (S ω) | m] =ᵐ[μ] fun ω => theta * q ω) :
    μ[fun ω => spinSign (S ω) |
      (inferInstance : MeasurableSpace ℝ).comap q] =ᵐ[μ] fun ω => theta * q ω := by
  have hle : (inferInstance : MeasurableSpace ℝ).comap q ≤ m := hq.comap_le
  have hTower := condExp_condExp_of_le (μ := μ)
    (f := fun ω => spinSign (S ω)) hle hm
  apply hTower.symm.trans
  apply (condExp_congr_ae hPost).trans
  have hqm : Measurable[(inferInstance : MeasurableSpace ℝ).comap q] q :=
    comap_measurable q
  rw [condExp_of_stronglyMeasurable (μ := μ) (f := fun ω => theta * q ω)
    (hle.trans hm) (hqm.const_mul theta).stronglyMeasurable (hqi.const_mul theta)]

theorem condDistrib_statistic_eq_tilt_of_linear_posterior
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {S : Ω → IsingSpin}
    {q : Ω → ℝ} {theta : ℝ} (hm : m ≤ mΩ) (hS : Measurable S)
    (hq : Measurable[m] q) (hqi : Integrable q μ)
    (hPost : μ[fun ω => spinSign (S ω) | m] =ᵐ[μ] fun ω => theta * q ω)
    (hFair : ∀ a : IsingSpin, μ {ω | S ω = a} = (1 / 2 : ENNReal))
    (a : IsingSpin) :
    condDistrib q S μ a = linearSignalTilt (μ.map q) id (spinSign a * theta) := by
  have hqa : Measurable q := hq.mono hm le_rfl
  rw [condDistrib_eq_map_cond_fiber hS hqa a (by
    change μ {ω | S ω = a} ≠ 0
    rw [hFair]
    norm_num)]
  change (μ[|{ω | S ω = a}]).map q = _
  rw [map_cond_spin_observation_eq_linearSignalTilt hS hqa
    (measurable_id.const_mul theta)
    (condExp_spin_statistic_of_linear_posterior hm hq hqi hPost) a (hFair a)]
  unfold linearSignalTilt
  congr 1
  funext y
  congr 1
  simp only [id_eq]
  ring

end Problem367

end

end OAI
