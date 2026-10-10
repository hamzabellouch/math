import OAI.Probability.InvariantIsing.Pressure.RandomOrbitTail
import OAI.Probability.InvariantIsing.Pressure.RandomSpectralBound
import OAI.Probability.InvariantIsing.Pressure.LocalizedAlmostSure

namespace OAI

/-! Almost-sure conditional Haar concentration for random spectra and fields. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace InvariantIsing

theorem ae_random_orbit_pressure_sub_mean (hhaar : HaarConcentrationInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : (N : ℕ) → Ω → FieldSpectralData N) (Y : ℕ → Ω → ℝ)
    (hd : ∀ N, Measurable (d N)) (hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (hlaw : ∀ N, ConditionalFieldOrbitLaw P (d N) (Y N) (H N))
    (hbound : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ᶠ k in atTop, spectralRadius ((d (k+1) ω).1) ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun k => Y (k+1) ω-
      ∫ U, dataPhysicalPressure (d (k+1) ω) U ∂H (k+1)) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_localized_exponential_tail P
    (fun k ω => Y (k+1) ω-∫ U, dataPhysicalPressure (d (k+1) ω) U ∂H (k+1))
    (fun k ω => spectralRadius ((d (k+1) ω).1)) _ hbound
  intro K ε hK hε
  obtain ⟨C,a,hC,ha,ht⟩ := uniform_physical_pressure_mean_tail hhaar
  obtain ⟨N₀,hN₀⟩ := ht K ε hK hε
  refine ⟨C,a*(ε/2)^2/K^2,hC.le,by positivity,max N₀ 3,?_⟩
  intro n hn
  have hb := conditional_orbit_tail_bound (Nat.succ_pos n) P (d (n+1)) (Y (n+1))
    (hd (n+1)) (hY (n+1)) (H (n+1)) (hlaw (n+1)) K ε
    (C*Real.exp (-a*(n+1 : ℝ)*(ε/2)^2/K^2)) (fun data hdata => by
      simpa only [dataPhysicalPressure,Nat.cast_add,Nat.cast_one] using
        hN₀ (n+1) (by omega) (by omega) (H (n+1)) inferInstance inferInstance
          data.1 data.2 hdata)
  have he : {ω | (∀ i, |(d (n+1) ω).1 i| ≤ K) ∧
      ε ≤ |Y (n+1) ω-∫ U, dataPhysicalPressure (d (n+1) ω) U ∂H (n+1)|}=
      {ω | ε ≤ |Y (n+1) ω-∫ U, dataPhysicalPressure (d (n+1) ω) U ∂H (n+1)| ∧
        spectralRadius ((d (n+1) ω).1) ≤ K} := by
    ext ω
    simp only [mem_ofPred_eq,spectralRadius_le_iff,and_comm]
  rw [he] at hb
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hb
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  refine hreal.trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have hc : 0 ≤ a*(ε/2)^2/K^2 := by positivity
  calc
    -a*(n+1 : ℝ)*(ε/2)^2/K^2= -(a*(ε/2)^2/K^2)*((n : ℝ)+1) := by ring
    _ ≤ -(a*(ε/2)^2/K^2)*(n : ℝ) := by nlinarith

end InvariantIsing

end

end OAI
