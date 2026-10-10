import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonLogSaving
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonEnergy

namespace OAI

/-! The restored common-factor remainder for the literal early-stopped
coefficient. All boundedness and active roughness facts are derived from
its original finite formula. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_early_divisor_common_log_saving (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve) {ξ κ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ) (hΦ' : ContDiff ℝ ∞ Φ) (k : ℕ) :
    ∃ (K : ℝ) (j : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b A u : ℝ), 0 < δ → δ ≤ 1 → X^κ ≤ b → b ≤ X →
      b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(3*k) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (e d : Eisenstein), primary d → norm d ≤ b^(1/1000:ℝ) →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      (Real.log X)^(6*(j+k)) ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      (norm d)^4 ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      ‖divisorDispersionVariance d S β u Φ A-divisorCoprimeDispersionGram d S β u Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  obtain ⟨K,j,hK,hbound⟩ := bounded_rough_divisor_common_log_saving hpnt hHuxley hκ Φ hΦ hΦ' k
  obtain ⟨M,hM,hcoeff⟩ := stopped_interval_energy (ι := ι) hξ hξz
  refine ⟨K*M^2,j,by positivity,?_⟩
  filter_upwards [hbound,hcoeff,eventually_ge_atTop (Real.exp 1)] with X hbound hcoeff hX
  intro δ b A u hδ hδone hbX hbXhi hAlo hAhi W hW e d hd hdhi j₀ k₀ h Z Q early hj hR hdR
  dsimp only
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hbp : 0 < b := (Real.rpow_pos_of_pos hXp _).trans_le hbX
  have hw : 0 < X^ξ := Real.rpow_pos_of_pos hXp _
  have hwz : X^ξ ≤ X^(2/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 hξz
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  have hs : ∀ a ∈ S, primary a ∧ Squarefree a ∧ b/2 ≤ norm a ∧ norm a ≤ b := by
    intro a ha
    have hp := stoppedIntervalSupport_spec X (b/2) b e ha
    exact ⟨hp.1,hp.2.1,(Finset.mem_filter.mp ha).2.2.2.1.le,hp.2.2⟩
  have hbnd : ∀ a ∈ S, ‖β a‖ ≤ M :=
    (hcoeff W hW _ 0 (b/2) b e hbp.le hbXhi).1
  have hr : ∀ a ∈ S, β a ≠ 0 → ∀ p, primaryPrime p → p ∣ a →
      min (X^ξ) (geometricBinLower (1+δ) X h) ≤ norm p := by
    intro a _ ha p hp hpa
    exact stoppedRowCoefficient_early_roughness X (X^ξ) (X^(2/5:ℝ)) 0 (1+δ) Z Q W
      hw hwz (by linarith) (by linarith) j₀ k₀ h early hj ha hp hpa
  have hb := hbound S β b A M u (min (X^ξ) (geometricBinLower (1+δ) X h)) d
    hbX hbXhi hAlo hAhi hM.le hR hd hdhi hdR hs hbnd hr
  exact hb.trans_eq (by ring)

end CubicFirstMoment

end

end OAI
