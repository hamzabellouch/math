import OAI.NumberTheory.JointDickman.Counting.PositiveFirstFormEnergy

namespace OAI

/-! # The positive energy forced by a nonzero mixed bin-label correlation -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def movingBinLabel {ι : Type*} [Fintype ι]
    (J : ℕ) (k : ι → ℕ) (z : ι → ℂ) (N n : ℕ) : ℂ :=
  binLabel (fun i => primeBin (N : ℝ) J (k i)) z n

theorem binLabel_energy_of_amplified_limit {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (H : ℕ → ℕ → ℂ) (s : ℕ → ℕ) (hs : StrictMono s)
    {B T : ℕ} (hB : 1 < B) (hT : 0 < T) (L : ℕ) (τ C : ℝ)
    {δ : ℝ} (hδ : 0 < δ) {w : ℂ} (hw : 2*δ ≤ ‖w‖)
    (hl : Tendsto (fun N => (∑ n ∈ range (s N),
      (star (movingBinLabel J k z (s N) n) * H (s N) n) *
        (arithmeticSubsetAmplification B L τ C (amplificationSmoothWeight B T) n : ℂ)) /
        (s N : ℂ)) atTop (nhds w)) :
    ∀ᶠ N : ℕ in atTop, δ^2/2 ≤
      firstFormEnergy B L τ C (amplificationOuterWeight B)
        (amplificationInnerWeight T) (H (s N)) (s N) / ((B : ℝ)*T) := by
  have hv := activeFirstFormVolume_bound hB L τ C (amplificationOuterWeight B) hT
    (fun c => amplificationBump_bounds _)
  have hf := binLabel_amplification_first_form J hJ k hk z B L τ C
    (amplificationOuterWeight B) (amplificationInnerWeight T) H
  filter_upwards [norm_eventually_lower hδ hw hl, hs.tendsto_atTop.eventually hv,
    hs.tendsto_atTop.eventually hf] with N hlow hvol hform
  apply firstFormEnergy_lower (Nat.zero_lt_of_lt hB) hT L τ C
    (amplificationOuterWeight B) (amplificationInnerWeight T)
    (movingBinLabel J k z (s N)) (H (s N)) (s N) hδ.le
    (fun c => (amplificationBump_bounds _).1)
    (fun m => norm_binLabel_le_one _ z hz m)
    (fun a c h => amplificationBump_ratio_lower T a c h) _ hvol
  change δ ≤ ‖(∑ n ∈ range (s N),
    (star (binLabel (fun i => primeBin (s N : ℝ) J (k i)) z n) * H (s N) n) *
      (arithmeticSubsetAmplification B L τ C
        (fun a c => amplificationOuterWeight B c * amplificationInnerWeight T a c) n : ℂ)) /
        (s N : ℂ)‖ at hlow
  rw [hform, norm_mul, norm_div, norm_one, Complex.norm_natCast,
    one_div_mul_eq_div] at hlow
  have hBr : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hgfun : movingBinLabel J k z (s N) =
      (binLabel (fun i => primeBin (s N : ℝ) J (k i)) z : ℕ → ℂ) := by
    funext n
    rfl
  rw [hgfun]
  simpa only [mul_comm] using (le_div_iff₀ hBr).mp hlow

/-- The subsequence and the positive constant are constructed from the
original mixed mean. The analytic assumptions are published inputs; the energy constant is independent of the later cutoff C. -/
theorem nonzero_binLabel_correlation_forces_energy
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (H : ℕ → ℕ → ℂ) (hH : ∀ N n, ‖H N n‖ ≤ 2) {β : ℂ} (hβ : β ≠ 0)
    (hmean : Tendsto (fun N => (∑ n ∈ range N,
      star (movingBinLabel J k z N n) * H N n)/(N : ℂ)) atTop (nhds β)) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ e : ℝ, 0 < e ∧
      ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ → ∃ C₀ : ℝ, 0 ≤ C₀ ∧
        ∀ C : ℝ, C₀ ≤ C → ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
          e ≤ firstFormEnergy B L τ C (amplificationOuterWeight B)
            (amplificationInnerWeight (amplificationMultiplier B)) (H (s N)) (s N) /
              ((B : ℝ)*amplificationMultiplier B) := by
  let A : ℕ → ℕ → ℂ := fun N n => star (movingBinLabel J k z N n) * H N n
  have hA : ∀ N n, ‖A N n‖ ≤ 2 := by
    intro N n
    dsimp only [A]
    rw [norm_mul, norm_star]
    have hg := norm_binLabel_le_one (fun i => primeBin (N : ℝ) J (k i)) z hz n
    exact (mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans (by simpa using hH N n)
  obtain ⟨s,hs,W,hW,hl⟩ := exists_arithmetic_amplification_profile A (by norm_num) hA hmean
  obtain ⟨d,hd,hdB⟩ := smooth_amplified_profile_lower hFord hSD hM hMP W (by rwa [hW])
  let δ : ℝ := d * ‖β‖ / 2
  have hδ : 0 < δ := div_pos (mul_pos hd (norm_pos_iff.mpr hβ)) (by norm_num)
  refine ⟨s,hs,δ^2/2,div_pos (sq_pos_of_pos hδ) (by norm_num),?_⟩
  intro L τ hL hτ
  obtain ⟨C₀,hC₀,hCb⟩ := hdB L τ hL hτ
  refine ⟨C₀,hC₀,?_⟩
  intro C hC
  filter_upwards [hCb C hC amplificationMultiplier amplificationMultiplier_valid,
    amplificationMultiplier_valid,eventually_gt_atTop 1] with B hBW hTB hB
  apply binLabel_energy_of_amplified_limit J hJ k hk z hz H s hs hB hTB.1 L τ C hδ
    (w := W.correlation (amplificationPeriod B)
      (smoothResidueAmplification B L τ C (amplificationMultiplier B)))
  · rw [hW] at hBW
    dsimp only [δ]
    linarith
  · exact hl B L τ C (amplificationMultiplier B)

end JointDickman

end OAI
