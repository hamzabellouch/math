import OAI.NumberTheory.JointDickman.Amplification.SubsequenceAmplifiedProfile
import OAI.NumberTheory.JointDickman.Amplification.PositiveArithmeticGraph

namespace OAI

/-! # Positive amplification energy inside a prescribed bad subsequence -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem nonzero_binLabel_correlation_along_forces_energy
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (H : ℕ → ℕ → ℂ) (hH : ∀ N n, ‖H N n‖ ≤ 2)
    (r : ℕ → ℕ) (hr : StrictMono r) {β : ℂ} (hβ : β ≠ 0)
    (hmean : Tendsto (fun N => (∑ n ∈ range (r N),
      star (movingBinLabel J k z (r N) n) * H (r N) n)/(r N : ℂ)) atTop (nhds β)) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ e : ℝ, 0 < e ∧
      ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ → ∃ C₀ : ℝ, 0 ≤ C₀ ∧
        ∀ C : ℝ, C₀ ≤ C → ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
          e ≤ firstFormEnergy B L τ C (amplificationOuterWeight B)
            (amplificationInnerWeight (amplificationMultiplier B)) (H (r (s N))) (r (s N)) /
              ((B : ℝ)*amplificationMultiplier B) := by
  let A : ℕ → ℕ → ℂ := fun N n => star (movingBinLabel J k z N n) * H N n
  have hA : ∀ N n, ‖A N n‖ ≤ 2 := by
    intro N n
    dsimp only [A]
    rw [norm_mul,norm_star]
    have hg := norm_binLabel_le_one (fun i => primeBin (N : ℝ) J (k i)) z hz n
    exact (mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans (by simpa using hH N n)
  obtain ⟨s,hs,W,hW,hl⟩ := exists_arithmetic_amplification_profile_along A (by norm_num) hA r hr hmean
  obtain ⟨d,hd,hdB⟩ := smooth_amplified_profile_lower hFord hSD hM hMP W (by rwa [hW])
  let δ : ℝ := d*‖β‖/2
  have hδ : 0 < δ := div_pos (mul_pos hd (norm_pos_iff.mpr hβ)) (by norm_num)
  refine ⟨s,hs,δ^2/2,div_pos (sq_pos_of_pos hδ) (by norm_num),?_⟩
  intro L τ hL hτ
  obtain ⟨C₀,hC₀,hCb⟩ := hdB L τ hL hτ
  refine ⟨C₀,hC₀,?_⟩
  intro C hC
  filter_upwards [hCb C hC amplificationMultiplier amplificationMultiplier_valid,
    amplificationMultiplier_valid,eventually_gt_atTop 1] with B hBW hTB hB
  apply binLabel_energy_of_amplified_limit J hJ k hk z hz H (r ∘ s) (hr.comp hs) hB hTB.1 L τ C hδ
    (w := W.correlation (amplificationPeriod B)
      (smoothResidueAmplification B L τ C (amplificationMultiplier B)))
  · rw [hW] at hBW
    dsimp only [δ]
    linarith
  · exact hl B L τ C (amplificationMultiplier B)

end JointDickman

end OAI
