import OAI.Analysis.FiniteFactor.Sampling.Fourier
import OAI.Analysis.FiniteFactor.OrbitSampling.Powers

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

theorem sourceBlockSize_monotone : Monotone sourceBlockSize := by
  apply monotone_nat_of_le_succ
  intro s
  have hp := (sourceStage (s+1)).previous_size
  have hd : (sourceBlockSize s : ℝ) ≤ (sourceStageState (s+1)).d := by
    change (sourceBlockSize s : ℝ) ≤ ((sourceStageState s).d+(sourceStage s).m : ℕ)
    change ((sourceStage s).m : ℝ) ≤ ((sourceStageState s).d+(sourceStage s).m : ℕ)
    push_cast
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hm : (sourceBlockSize s : ℝ) ≤ sourceBlockSize (s+1) := by
    change ((sourceStageState (s+1)).d : ℝ) ≤ (sourceBlockSize (s+1) : ℝ)/100 at hp
    have := Nat.cast_nonneg (α := ℝ) (sourceBlockSize (s+1))
    linarith
  exact_mod_cast hm

theorem sourceFrequencyScale_monotone :
    Monotone (fun s => sourceBlockSize s * (sourceStageState s).K) := by
  have hK : Monotone (fun s => (sourceStageState s).K) := by
    apply monotone_nat_of_le_succ
    intro s
    have := sourceStage_cutoff_growth s
    omega
  intro s t hst
  exact Nat.mul_le_mul (sourceBlockSize_monotone hst) (hK hst)

/-- The full infinite-product angle expectation has the same coordinate
Fourier estimate; no independence between two phases is asserted. -/
theorem sourceAngleLaw_pair_fourier_le (i : SourceCoordinate) (v v' : ℤ) (n n' : ℝ)
    (hw : (v : ℝ)*n+(v' : ℝ)*n' ≠ 0) :
    ‖∫ θ, Complex.exp (2 * Real.pi * Complex.I *
      ((v : ℂ) * (Int.fract (n*θ i) : ℝ) + (v' : ℂ) * (Int.fract (n'*θ i) : ℝ)))
      ∂sourceAngleLaw‖ ≤
      1/(Real.pi*sourceAngleUnit i*|(v : ℝ)*n+(v' : ℝ)*n'|) := by
  have hh := sourceAngle_pair_fourier_le i v v' n n' hw
  simp_rw [pair_fourier_fract] at hh ⊢
  rw [← sourceAngleLaw_coordinate i,
    integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)] at hh
  exact hh

theorem sourceSampling_pair_fourier_bound (s : ℕ) (hs : 200000 ≤ sourceBlockSize s)
    (i : SourceCoordinate) (hi : i.1 ≤ s) (n n' : ℤ)
    (hn : n ∈ sourceSamplingPowers s) (hn' : n' ∈ sourceSamplingPowers s) (hne : n ≠ n')
    (v v' : ℤ) (hv : |v| ≤ (samplingH (sourceBlockSize s) : ℤ))
    (hv' : |v'| ≤ (samplingH (sourceBlockSize s) : ℤ)) (hvv' : v ≠ 0 ∨ v' ≠ 0) :
    ‖∫ θ, Complex.exp (2 * Real.pi * Complex.I *
      ((v : ℂ) * (Int.fract ((n : ℝ)*θ i) : ℝ) +
       (v' : ℂ) * (Int.fract ((n' : ℝ)*θ i) : ℝ))) ∂sourceAngleLaw‖ ≤
      Real.pi⁻¹*(sourceBlockSize s : ℝ)^(-1000 : ℝ) := by
  have hsep := (sourceSamplingPowers_spec s hs).2.2 hn hn' hne
  have hfreq : (samplingR (sourceBlockSize s) (sourceStageState s).K : ℤ) < |v*n+v'*n'| := by
    by_contra hh
    exact hsep ⟨v,mem_Icc.mpr (abs_le.mp hv),v',mem_Icc.mpr (abs_le.mp hv'),hvv',le_of_not_gt hh⟩
  let w : ℝ := (v : ℝ)*(n : ℝ)+(v' : ℝ)*(n' : ℝ)
  have hwR : (samplingR (sourceBlockSize s) (sourceStageState s).K : ℝ) < |w| := by
    dsimp [w]
    exact_mod_cast hfreq
  have hwpos : 0 < |w| := lt_of_le_of_lt (Nat.cast_nonneg _) hwR
  have hw : w ≠ 0 := abs_pos.mp hwpos
  apply (sourceAngleLaw_pair_fourier_le i v v' (n : ℝ) (n' : ℝ) hw).trans
  have hN : (sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K ≤
      (sourceBlockSize s : ℝ)*(sourceStageState s).K := by
    exact_mod_cast sourceFrequencyScale_monotone hi
  have hmpos := sourceBlockSize_pos s
  have hNpos := mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1)
  have hscale : (sourceBlockSize s : ℝ)^1000 ≤ sourceAngleUnit i * |w| := by
    unfold samplingR at hwR
    push_cast at hwR
    unfold sourceAngleUnit
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hNpos]
    have hh := mul_le_mul_of_nonneg_right hN (pow_nonneg hmpos.le 1000)
    nlinarith
  change 1/(Real.pi*sourceAngleUnit i*|w|) ≤ _
  calc
    _ = Real.pi⁻¹*(1/(sourceAngleUnit i*|w|)) := by ring
    _ ≤ Real.pi⁻¹*(1/(sourceBlockSize s : ℝ)^1000) := by
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (pow_pos hmpos 1000) hscale) (inv_nonneg.mpr Real.pi_pos.le)
    _ = _ := by rw [Real.rpow_neg, Real.rpow_ofNat, one_div]; positivity

end
end FiniteFactor

end OAI
