import OAI.Probability.InvariantIsing.Pressure.UniformHaarMeanTail
import OAI.Probability.InvariantIsing.Cavity.CavityOrientedFamily
import OAI.Probability.InvariantIsing.Spectral.SpectralCountComparison

namespace OAI

/-! A dimension-uniform centered tail for the physical Haar pressure, independent
of the external field. This can be conditioned on random spectral and field data. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem uniform_physical_pressure_mean_tail (hpub : HaarConcentrationInput) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      ∀ K ε : ℝ, 0 < K → 0 < ε → ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 3 ≤ N →
      ∀ μ : Measure (Orthogonal N), IsProbabilityMeasure μ → μ.IsMulRightInvariant →
      ∀ eig c : Fin N → ℝ, (∀ i, |eig i| ≤ K) →
      μ.real {U | ε ≤ |rotatedPressure eig (matrixRotation U⁻¹) c-
        ∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ|} ≤
        C*Real.exp (-a*(N : ℝ)*(ε/2)^2/K^2) := by
  obtain ⟨C,a,hC,ha,ht⟩ := uniform_bounded_haar_mean_tail hpub
  refine ⟨C,a,hC,ha,?_⟩
  intro K ε hK hε
  obtain ⟨N₀,hN₀⟩ := ht K ε hK hε
  refine ⟨N₀,?_⟩
  intro N hN hN3 μ hμ hHaar eig c heig
  let : IsProbabilityMeasure μ := hμ
  let : μ.IsMulRightInvariant := hHaar
  have hpos : 0 < N := by omega
  let η := cavityOrientedBaseLaw hpos μ
  let f := fun U : SpecialOrthogonal N => rotatedPressure eig (specialRotation U) c-noninteractingPressure c
  have hf : Measurable f := (measurable_rotatedPressure eig c).sub_const _
  have hfb U : |f U| ≤ K :=
    (abs_pressure_sub_noninteracting_le hpos eig c (specialRotation U) K heig).trans (by linarith)
  have hlip U V : |f U-f V| ≤ K*frobeniusDistance U V := by
    dsimp only [f]
    rw [sub_sub_sub_cancel_right]
    exact abs_rotatedPressure_sub_rotation_le hpos eig U V c K hK.le heig
  have hh := hN₀ N hN hN3 η inferInstance (cavityOrientedBaseLaw_leftInvariant hpos μ)
    f hf hfb hlip
  have hmean : (∫ U, f U ∂η)=
      (∫ V, rotatedPressure eig (matrixRotation V⁻¹) c ∂μ)-noninteractingPressure c := by
    rw [integral_sub (integrable_countPressure hpos η eig c K heig) (integrable_const _)]
    simp only [integral_const,probReal_univ,one_smul]
    rw [cavity_oriented_pressure]
  have hset : MeasurableSet {U | ε ≤ |f U-(∫ V, f V ∂η)|} :=
    measurableSet_le measurable_const (hf.sub_const _).abs
  change (cavityOrientedBaseLaw hpos μ).real _ ≤ _ at hh
  have hT : Measurable (fun V : Orthogonal N => cavityOrientationLift hpos V⁻¹) :=
    (measurable_cavityOrientationLift hpos).comp measurable_inv
  rw [measureReal_def,cavityOrientedBaseLaw,Measure.map_apply hT hset] at hh
  convert hh using 1
  congr 1
  ext U
  change (ε ≤ |_ - _|) ↔ (ε ≤ |_ - _|)
  rw [hmean]
  simp only [f,rotatedPressure,cavityOrientationLift_energy]
  ring_nf

end InvariantIsing

end

end OAI
