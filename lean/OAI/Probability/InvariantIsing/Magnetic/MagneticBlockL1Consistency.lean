import OAI.Probability.InvariantIsing.Arrays.OverlapTestTransport
import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockPathConvergence

namespace OAI

/-! The constrained block overlap converges in L1 once its physical
weak tests hold along a sequence of growing blocks. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem magnetic_block_l1_of_constrained_tests {m : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a) (mag : ℕ → A → ℝ)
    {s : ℝ} (hs : s < 1) (hmag : ∀ r a, |mag r a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ) = spinGroupSize (group r) a * ((1+mag r a)/2))
    (p : OverlapPath)
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto (fun r => ∫ t, Φ (cavityStrictUniformPath p r t) *
      (restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
        (spinGroupSlice_nonempty (group r) (k r) (hk r))
        (cavityStrictUniformField rho lam hrho hsum p r) t - cavityStrictUniformPath p r t)
      ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun r => ∫ t, |restrictedBlockOverlapPath (hN r)
      (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
      (cavityStrictUniformField rho lam hrho hsum p r) t-p t| ∂pathMeasure) atTop (𝓝 0) := by
  let h := cavityStrictUniformField rho lam hrho hsum p
  let a := fun r => restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
    (spinGroupSlice_nonempty (group r) (k r) (hk r)) (h r)
  let b := fun r => magneticBlockPath (hN r) (h r) (fun j => mag r (group r j))
  have hab := magneticBlockPath_l1_tendsto N hN hNlim group k hk mag hs hmag hc h
    (fun r => cavityStrictUniformField_height_le rho lam hrho hsum hK hlam p r (Fin.last r))
  have hab' : Tendsto (fun r => ∫ t, |b r t-a r t| ∂pathMeasure) atTop (𝓝 0) := by
    simpa only [abs_sub_comm] using hab
  have hb : Tendsto (fun r => ∫ t, |b r t-p t| ∂pathMeasure) atTop (𝓝 0) := by
    apply cavity_strict_magnetic_block_self_consistency rho lam hrho hsum hK hlam N hN
      (fun r j => mag r (group r j)) p
    intro Φ
    have hd := overlap_weighted_test_l1_transport (cavityStrictUniformPath p) b a hab' Φ
    have ht := hd.add (htest Φ)
    simpa only [a, b, h, sub_add_cancel, add_zero] using ht
  have hz : Tendsto (fun r => (∫ t, |a r t-b r t| ∂pathMeasure) +
      ∫ t, |b r t-p t| ∂pathMeasure) atTop (𝓝 0) := by simpa using hab.add hb
  apply squeeze_zero (fun r => integral_nonneg (fun t => abs_nonneg _)) (fun r => ?_) hz
  calc
    (∫ t, |a r t-p t| ∂pathMeasure) ≤ ∫ t, (|a r t-b r t|+|b r t-p t|) ∂pathMeasure :=
      integral_mono ((a r).integrable.sub p.integrable).abs
        (((a r).integrable.sub (b r).integrable).abs.add (((b r).integrable.sub p.integrable).abs))
        (fun t => abs_sub_le (a r t) (b r t) (p t))
    _ = _ := integral_add ((a r).integrable.sub (b r).integrable).abs
      ((b r).integrable.sub p.integrable).abs

end InvariantIsing

end

end OAI
