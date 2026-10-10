import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingParameters
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalDensity

namespace OAI

/-! Uniform finite-interval density for the actual working prime bands.
The outer and working-parameter thresholds are independent. -/

namespace TwoPointCorrelations

open Filter Finset
open scoped Classical

/-- The explicit natural-indexed bands have the same density estimate on
every translated interval of length at least the original outer cutoff. -/
theorem mrt_actual_band_interval_density :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (P Q : ℝ) (J : ℕ), 2 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤
        Real.exp (Real.sqrt (Real.log (X:ℝ))/2)) →
      ∀ (A N : ℕ) [NeZero N], X ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))
          (A+n.val)) ≤ C*Real.log P/Real.log Q := by
  obtain ⟨C,hC,hd⟩ := mrt_typical_density
  have hlog : Tendsto (fun X:ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C,hC,?_⟩
  filter_upwards [hlog.eventually hd,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),eventually_ge_atTop (2:ℕ)]
    with X hd hL hX
  intro P Q J hP hPQ hQ hu A N _ hXN
  have hXp : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have hu' : ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤
      Real.exp ((Real.log (X:ℝ))^(99/100:ℝ)) := by
    intro j hj
    apply (hu j hj).trans (Real.exp_le_exp.mpr ?_)
    exact (by nlinarith [Real.sqrt_nonneg (Real.log (X:ℝ))] :
      Real.sqrt (Real.log (X:ℝ))/2 ≤ Real.sqrt (Real.log (X:ℝ))).trans
      (mrt_common_density_power hL)
  have hsize : (1/2:ℝ)*Real.exp ((Real.log (X:ℝ))^(199/200:ℝ)) ≤ N := by
    calc
      _ ≤ Real.exp ((Real.log (X:ℝ))^(199/200:ℝ)) := by
        nlinarith [Real.exp_pos ((Real.log (X:ℝ))^(199/200:ℝ))]
      _ ≤ Real.exp (Real.log (X:ℝ)) := Real.exp_le_exp.mpr
        (Real.rpow_le_self_of_one_le hL (by norm_num))
      _ = (X:ℝ) := Real.exp_log hXp
      _ ≤ N := by exact_mod_cast hXN
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  have heq (n:ℕ) : mrtTypical univ
      (fun j : {j:ℕ // j ∈ (Icc 1 J : Finset ℕ)} => V j) n ↔
      mrtTypical (Icc 1 J) V n := by simp [mrtTypical]
  have hp := hd P Q J hP hPQ hQ hu' A N hsize
  change (uniformFiniteLaw (Fin N)).probability
    (fun n => ¬mrtTypical univ
      (fun j : {j:ℕ // j ∈ (Icc 1 J : Finset ℕ)} => V j) (A+n.val)) ≤ _ at hp
  simpa only [heq] using hp

/-- For the actual working first band the missing density has exactly the
working error rate, uniformly in translation and all longer intervals. -/
theorem mrt_working_interval_density :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℝ, ∃ X₀ : ℕ,
      ∀ W : ℝ, W₀ ≤ W → ∀ H : ℕ, 0 < H →
      1 ≤ Real.log (H:ℝ) → W ≤ Real.log (H:ℝ)^5 →
      ∀ X : ℕ, X₀ ≤ X → ∀ J : ℕ,
      let P := W^(500000:ℕ)
      let Q := (majorArcWorkingLength H W:ℝ)/W^3
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤
        Real.exp (Real.sqrt (Real.log (X:ℝ))/2)) →
      ∀ (A N : ℕ) [NeZero N], X ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))
          (A+n.val)) ≤ C*majorArcWorkingError W := by
  obtain ⟨C,hC,hd⟩ := mrt_actual_band_interval_density
  obtain ⟨X₀,hX₀⟩ := Filter.eventually_atTop.mp hd
  have hw := (mrt_working_prime_parameters.and
    ((major_arc_working_length_power 6).and major_arc_working_cap_log))
  obtain ⟨W₀,hW₀⟩ := Filter.eventually_atTop.mp hw
  refine ⟨C*(8*500000),by positivity,W₀,X₀,?_⟩
  intro W hW H hH hLH hWH X hX J
  dsimp only
  intro hu A N _ hXN
  have hw := hW₀ W hW
  have hp := hw.1.2 H hH hLH hWH
  have hb := major_arc_working_band_density 500000 hw.1.1 hLH hWH
    (hw.2.1 H hH hLH hWH) hw.2.2
  have hd := hX₀ X hX (W^(500000:ℕ))
    ((majorArcWorkingLength H W:ℝ)/W^3) J hp.1 hp.2.1 hp.2.2.2.1 hu A N hXN
  calc
    _ ≤ C*Real.log (W^(500000:ℕ))/
        Real.log ((majorArcWorkingLength H W:ℝ)/W^3) := hd
    _ = C*(Real.log (W^(500000:ℕ))/
        Real.log ((majorArcWorkingLength H W:ℝ)/W^3)) := by ring
    _ ≤ C*(8*(500000:ℝ)*majorArcWorkingError W) :=
      mul_le_mul_of_nonneg_left hb hC.le
    _ = _ := by ring

end TwoPointCorrelations

end OAI
