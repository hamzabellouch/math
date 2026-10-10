import OAI.NumberTheory.JointDickman.Arithmetic.RationalBinSmooth
import OAI.NumberTheory.JointDickman.Amplification.BinJointEventsDischarge

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem fixedDensity_common_denominator_proved
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    (hBill : FiniteBinDistributionInput)
    {J k l : ℕ} (hJ : 2 ≤ J) (hk : 0 < k) (hkj : k < J) (hl : 0 < l) (hlj : l < J) :
    Tendsto (fixedDensity ((k : ℝ)/J) ((l : ℝ)/J)) atTop
      (𝓝 (dickmanCDF ((k : ℝ)/J)*dickmanCDF ((l : ℝ)/J))) := by
  obtain ⟨ν,hν,hνone,hνmean,hCDF⟩ := hBill J hJ
  have hh := bin_joint_event_limit_proved hKMT hFord hSD hSW hM hMP hMC
    (by omega : 0 < J) ν hν hνone hνmean (higherBinEvent J k) (higherBinEvent J l)
  have hkCDF : (∑ r with higherBinEvent J k r, ν r) = dickmanCDF ((k : ℝ)/J) := by
    unfold higherBinEvent
    convert hCDF k hk hkj using 1
    congr 3
  have hlCDF : (∑ r with higherBinEvent J l r, ν r) = dickmanCDF ((l : ℝ)/J) := by
    unfold higherBinEvent
    convert hCDF l hl hlj using 1
    congr 3
  rw [hkCDF,hlCDF] at hh
  have hjoint : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      if fixedScaleEvent ((k : ℝ)/J) ((l : ℝ)/J) N n then (1 : ℂ) else 0)/(N : ℂ)) atTop
      (𝓝 (((dickmanCDF ((k : ℝ)/J) : ℝ) : ℂ)*(dickmanCDF ((l : ℝ)/J) : ℂ))) := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    congr 1
    apply sum_congr rfl
    intro n hn
    simp only [fixedScaleEvent_bin_equiv (by omega : 0 < J) hk hkj hl hlj hN (mem_range.mp hn)]
  have he := empirical_limit_of_range_limit (fun N => fixedScaleEvent ((k : ℝ)/J) ((l : ℝ)/J) N) hjoint
  have hr := (Complex.continuous_re.tendsto _).comp he
  change Tendsto (fun N => (empiricalCount (fixedScaleEvent ((k : ℝ)/J) ((l : ℝ)/J) N) N : ℝ)/N)
    atTop (𝓝 (dickmanCDF ((k : ℝ)/J)*dickmanCDF ((l : ℝ)/J)))
  simpa only [Function.comp_def,← Complex.ofReal_natCast,← Complex.ofReal_div,
    ← Complex.ofReal_mul,Complex.ofReal_re] using hr

end JointDickman

end OAI
