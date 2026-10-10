import OAI.NumberTheory.JointDickman.Amplification.BinJointEvents
import OAI.NumberTheory.JointDickman.Amplification.EmpiricalRangeTransfer
import OAI.NumberTheory.JointDickman.Amplification.MovingLimit

namespace OAI

/-! # The fixed-scale joint smoothness law at common-denominator thresholds -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem fixedScaleEvent_bin_equiv {J k l N n : ℕ}
    (hJ : 0 < J) (hk : 0 < k) (hkj : k < J) (hl : 0 < l) (hlj : l < J)
    (hN : 1 ≤ N) (hn : n < N) :
    (higherBinEvent J k (canonicalBinVector J (N : ℝ) n) ∧
      higherBinEvent J l (canonicalBinVector J (N : ℝ) (n+1))) ↔
      fixedScaleEvent ((k : ℝ)/J) ((l : ℝ)/J) N n := by
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hn0 : n = 0
  · subst n
    simp only [Nat.zero_add,canonicalBinVector_zero,canonicalBinVector_one,higherBinEvent,Pi.zero_apply,
      implies_true,true_and]
    simp [fixedScaleEvent,Real.rpow_nonneg,Real.one_le_rpow hx (show 0 ≤ (l : ℝ)/J by positivity)]
  · have hn1 : 1 ≤ n := by omega
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.le
    have hsN : (n+1 : ℕ) ≤ N := by omega
    rw [higherBinEvent_iff hJ hk,higherBinEvent_iff hJ hl]
    exact and_congr
      (maxPrimeFac_le_iff_higher_counts_zero hx hJ hkj.le hn1 hnN).symm
      (maxPrimeFac_le_iff_higher_counts_zero hx hJ hlj.le (by omega) (by exact_mod_cast hsN)).symm

theorem fixedDensity_common_denominator
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    (hBill : FiniteBinDistributionInput)
    {J k l : ℕ} (hJ : 2 ≤ J) (hk : 0 < k) (hkj : k < J) (hl : 0 < l) (hlj : l < J) :
    Tendsto (fixedDensity ((k : ℝ)/J) ((l : ℝ)/J)) atTop
      (𝓝 (dickmanCDF ((k : ℝ)/J)*dickmanCDF ((l : ℝ)/J))) := by
  obtain ⟨ν,hν,hνone,hνmean,hCDF⟩ := hBill J hJ
  have hh := bin_joint_event_limit hMR hMRT hKMT hFord hSD hSW hM hMP hMC
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
