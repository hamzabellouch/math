import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ProfileFrequencyEnergy

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

lemma scaled_three_axis_energy {L ℓ ε c C : ℝ} (hL : 0 < L) (hℓ : L ≤ ℓ)
    (hℓ' : ℓ ≤ 2*L) (hε : 0 ≤ ε) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hsmall : ε^2*C ≤ 1) (β : Fin 3 → ℝ)
    (hlo : c*L^2 ≤ ∑ i, (β i)^2) (hhi : (∑ i, (β i)^2) ≤ C*L^2) :
    (∀ i, |ε/ℓ*β i| ≤ 1) ∧ c*ε^2/4 ≤ ∑ i, (ε/ℓ*β i)^2 := by
  have hpos : 0 < ℓ := hL.trans_le hℓ
  have hrlo : (1/2 : ℝ) ≤ L/ℓ := (le_div_iff₀ hpos).mpr (by linarith)
  have hrhi : L/ℓ ≤ 1 := (div_le_iff₀ hpos).mpr (by simpa using hℓ)
  have hrrlo : (1/4 : ℝ) ≤ (L/ℓ)^2 := by nlinarith
  have hrrhi : (L/ℓ)^2 ≤ 1 := by nlinarith
  have heq : (∑ i, (ε/ℓ*β i)^2) = (ε/ℓ)^2*(∑ i, (β i)^2) := by
    simp only [mul_pow,Finset.mul_sum]
  have hlo' : c*ε^2/4 ≤ ∑ i, (ε/ℓ*β i)^2 := by
    rw [heq]
    calc
      _ ≤ c*ε^2*(L/ℓ)^2 := by
        have hmul := mul_le_mul_of_nonneg_left hrrlo (mul_nonneg hc (pow_nonneg hε 2))
        nlinarith
      _ = (ε/ℓ)^2*(c*L^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (sq_nonneg _)
  have hhi' : (∑ i, (ε/ℓ*β i)^2) ≤ 1 := by
    rw [heq]
    calc
      _ ≤ (ε/ℓ)^2*(C*L^2) := mul_le_mul_of_nonneg_left hhi (sq_nonneg _)
      _ = (ε^2*C)*(L/ℓ)^2 := by ring
      _ ≤ ε^2*C := mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) hC) hrrhi
      _ ≤ 1 := hsmall
  refine ⟨?_,hlo'⟩
  intro i
  have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
    (f := fun j => (ε/ℓ*β j)^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hi : (ε/ℓ*β i)^2 ≤ 1 := hs.trans hhi'
  rw [abs_le]
  constructor <;> nlinarith

theorem compact_packet_angular_gap (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ κ > 0, κ ≤ 1 ∧
      ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
      ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ z : Fin 3 → ℂ, ∀ x : NormalWaveSpace,
        (∑ i, z i*z i = -1) → ‖x-q.1‖ ≤ r →
        ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ r →
        ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
        let θ := fun i => ε/ℓ*normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (∀ i, |θ i| ≤ 1) ∧ κ ≤ ∑ i, (θ i)^2 := by
  obtain ⟨c,hc,C,hC,hb⟩ := compact_normal_profile_angular_energy g hK
  let ε := 1/(C+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := (div_le_iff₀ (by linarith : 0 < C+1)).mpr (by linarith)
  have hεC : ε^2*C ≤ 1 := by
    have he : ε*(C+1) = 1 := by dsimp [ε]; field_simp
    have hsq := sq_nonneg (ε*C)
    nlinarith [mul_nonneg hε.le hC.le]
  let κ := min 1 (c*ε^2/4)
  have hκ : 0 < κ := lt_min zero_lt_one (by positivity)
  refine ⟨ε,hε,hε1,κ,hκ,min_le_left _ _,?_⟩
  intro φ hφ
  obtain ⟨r,hr,he⟩ := hb φ hφ
  refine ⟨r,hr,?_⟩
  intro q hq z x hz hx hlin ℓ hℓ hℓ'
  obtain ⟨hlo,hhi⟩ := he q hq z x hz hx hlin
  have hh := scaled_three_axis_energy (lt_of_lt_of_le zero_lt_one (profileFrequencyScale_ge_one g φ x))
    hℓ hℓ' hε.le hc.le hC.le hεC
    (fun i => normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i)) hlo hhi
  exact ⟨hh.1,(min_le_right _ _).trans hh.2⟩
end YauCounterexamples
end

end OAI
