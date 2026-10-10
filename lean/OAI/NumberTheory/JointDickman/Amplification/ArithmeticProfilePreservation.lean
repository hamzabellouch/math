import OAI.NumberTheory.JointDickman.Amplification.ProfilePreservation

namespace OAI

/-! # Profile preservation for the manuscript's actual smooth divisor weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def amplificationPeriod (B : ℕ) : ℕ+ :=
  ⟨auxiliarySquarePeriod B, auxiliarySquarePeriod_pos B⟩

noncomputable def smoothResidueAmplification (B L : ℕ) (τ C : ℝ) (T : ℕ) :
    ZMod (amplificationPeriod B : ℕ) → ℂ :=
  fun a => (residueAmplification B L τ C (amplificationSmoothWeight B T) a : ℂ)

theorem smoothResidueAmplification_energy (B L : ℕ) (τ C : ℝ) (T : ℕ) :
    residueEnergy (smoothResidueAmplification B L τ C T) =
      arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B T) 2 := by
  unfold residueEnergy smoothResidueAmplification arithmeticAmplificationMoment
    residueAmplification amplificationPeriod
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rfl

theorem smoothResidueAmplification_mean (B L : ℕ) (τ C : ℝ) (T : ℕ) :
    residueMean (smoothResidueAmplification B L τ C T) =
      (arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B T) 1 : ℂ) :=
  residueAmplification_mean B L τ C (amplificationSmoothWeight B T)

/-- The precise preservation statement, using the actual arithmetic weight.
Only the previously cited sieve and Mertens inputs enter its moment bound. -/
theorem smooth_arithmetic_profile_preservation
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (W : ResidueProfile) (L : ℕ) (τ C : ℝ) (T : ℕ → ℕ)
    (hT : ∀ᶠ B : ℕ in atTop, 0 < T B ∧ (T B : ℝ) ≤ Real.exp ((1/10 : ℝ)*B)) :
    Tendsto (fun B => W.correlation (amplificationPeriod B)
      (smoothResidueAmplification B L τ C (T B)) - W.mean *
        (arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B (T B)) 1 : ℂ))
      atTop (nhds 0) := by
  have hcop (d : ℕ+) : ∀ᶠ B : ℕ in atTop,
      (d : ℕ).Coprime (amplificationPeriod B) := by
    filter_upwards [auxiliarySquarePeriod_eventually_coprime d d.pos] with B hB
    exact hB.symm
  obtain ⟨K,hK,hb⟩ := smooth_arithmetic_second_bound hFord hM L τ C
  have hm : ∀ᶠ B : ℕ in atTop,
      residueEnergy (smoothResidueAmplification B L τ C (T B)) ≤ K := by
    filter_upwards [hb,hT] with B hB hTB
    rw [smoothResidueAmplification_energy]
    exact hB (T B) hTB.1 hTB.2
  simpa only [smoothResidueAmplification_mean] using
    W.preservation amplificationPeriod (fun B => smoothResidueAmplification B L τ C (T B))
      hcop ⟨K,hK,hm⟩

end JointDickman

end OAI
