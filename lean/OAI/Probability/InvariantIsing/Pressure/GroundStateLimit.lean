import OAI.Probability.InvariantIsing.Pressure.PositiveTemperaturePressure
import OAI.Probability.InvariantIsing.Pressure.GroundStateMean
import OAI.Probability.InvariantIsing.Pressure.ThermalLimitSqueeze

namespace OAI

/-! The deterministic ground-state limit, almost surely and in expectation,
and the existence of the full real-temperature variational limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

def thermalVariationalValue (ν : ProbabilityMeasure ℝ) (b β : ℝ) : ℝ :=
  (variationalFunctional (measureR (scaledSpectralLaw ν β : Measure ℝ) (β*b))).toReal/β

theorem ground_state_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (hU : ∀ N, Measurable (U N))
    (hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    ∃ M : ℝ,
      Tendsto (fun N => ∫ ω, groundStateEnergy (eig N) (matrixRotation (U N ω)⁻¹) ∂P)
        atTop (𝓝 M) ∧
      (∀ᵐ ω ∂P, Tendsto (fun N => groundStateEnergy (eig N) (matrixRotation (U N ω)⁻¹))
        atTop (𝓝 M)) ∧
      Tendsto (thermalVariationalValue ν b) atTop (𝓝 M) := by
  let p := fun (k N : ℕ) => (∫ ω, rotatedPressure (fun i => ((k : ℝ)+1)*eig N i)
    (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)/((k : ℝ)+1)
  let v := fun k : ℕ => thermalVariationalValue ν b ((k : ℝ)+1)
  let g := fun N => ∫ ω, groundStateEnergy (eig N) (matrixRotation (U N ω)⁻¹) ∂P
  have hc : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hp (k : ℕ) : Tendsto (p k) atTop (𝓝 (v k)) :=
    ((positive_temperature_pressure hhaar hgauss hpub P U hU hHaar eig ν a b
      hbound ha hb hno ((k : ℝ)+1) (by positivity) hweak).1).div_const _
  have hmean (k : ℕ) : ∀ᶠ N in atTop, p k N ≤ g N ∧ g N ≤ p k N+Real.log 2/(k+1) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact mean_groundState_squeeze (by omega) P (U N) (hU N) (eig N) _ (by positivity)
  obtain ⟨M,hv,hg⟩ := exists_thermal_ground_limit p g v (Real.log 2) hc hp hmean
  refine ⟨M,hg,?_,?_⟩
  · have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, Tendsto
        (fun N => rotatedPressure (fun i => ((k : ℝ)+1)*eig N i)
          (matrixRotation (U N ω)⁻¹) (fun _ => 0)/((k : ℝ)+1)) atTop (𝓝 (v k)) := by
      apply ae_all_iff.mpr
      intro k
      filter_upwards [(positive_temperature_pressure hhaar hgauss hpub P U hU hHaar eig ν a b
        hbound ha hb hno ((k : ℝ)+1) (by positivity) hweak).2] with ω hω
      exact hω.div_const _
    filter_upwards [hall] with ω hω
    apply thermal_squeeze_tendsto _ _ v (Real.log 2) M hc hv hω
    intro k
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact groundStateEnergy_squeeze (by omega) (eig N) (matrixRotation (U N ω)⁻¹) _ (by positivity)
  · have hbounds (β : ℝ) (hβ : 0 < β) :
        thermalVariationalValue ν b β ≤ M ∧ M ≤ thermalVariationalValue ν b β+Real.log 2/β := by
      have ht := ((positive_temperature_pressure hhaar hgauss hpub P U hU hHaar eig ν a b
        hbound ha hb hno β hβ hweak).1).div_const β
      have he : ∀ᶠ N in atTop,
          (∫ ω, rotatedPressure (fun i => β*eig N i) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)/β ≤ g N ∧
          g N ≤ (∫ ω, rotatedPressure (fun i => β*eig N i) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)/β+
            Real.log 2/β := by
        filter_upwards [eventually_ge_atTop 1] with N hN
        exact mean_groundState_squeeze (by omega) P (U N) (hU N) (eig N) β hβ
      exact ⟨le_of_tendsto_of_tendsto ht hg (he.mono fun _ h => h.1),
        le_of_tendsto_of_tendsto hg (ht.add_const _) (he.mono fun _ h => h.2)⟩
    apply tendsto_sub_nhds_zero_iff.mp
    apply squeeze_zero_norm' _ (tendsto_id.const_div_atTop (Real.log 2))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    rw [Real.norm_eq_abs,abs_le]
    simp only [id_eq]
    have hh := hbounds β hβ
    constructor <;> linarith [hh.1,hh.2,div_nonneg hc hβ.le]

end InvariantIsing

end

end OAI
