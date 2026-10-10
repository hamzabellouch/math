import OAI.Probability.InvariantIsing.Arrays.OverlapTestTransport
import OAI.Probability.InvariantIsing.Cavity.CavityMagneticDiagonal
import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockPathConvergence

namespace OAI

/-! The constrained block overlap converges in L1 along a diagonal of growing blocks and varying base quantiles,
from its physical weak tests and almost-everywhere quantile convergence. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem magnetic_diagonal_l1_of_constrained_tests {m : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a) (mag : ℕ → A → ℝ)
    {s : ℝ} (hs : s < 1) (hmag : ∀ r a, |mag r a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ) = spinGroupSize (group r) a * ((1+mag r a)/2))
    (base : ℕ → OverlapPath) (depth : ℕ → ℕ) (p : OverlapPath)
    (hq : ∀ᵐ t ∂pathMeasure, Tendsto
      (fun r => cavityStrictUniformPath (base r) (depth r) t) atTop (𝓝 (p t)))
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto (fun r => ∫ t, Φ (cavityStrictUniformPath (base r) (depth r) t) *
      (restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
        (spinGroupSlice_nonempty (group r) (k r) (hk r))
        (cavityStrictUniformField rho lam hrho hsum (base r) (depth r)) t - cavityStrictUniformPath (base r) (depth r) t)
      ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun r => ∫ t, |restrictedBlockOverlapPath (hN r)
      (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
      (cavityStrictUniformField rho lam hrho hsum (base r) (depth r)) t-p t| ∂pathMeasure) atTop (𝓝 0) := by
  let h := fun r => cavityStrictUniformField rho lam hrho hsum (base r) (depth r)
  let a := fun r => restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
    (spinGroupSlice_nonempty (group r) (k r) (hk r)) (h r)
  let b := fun r => magneticBlockPath (hN r) (h r) (fun j => mag r (group r j))
  have hab := magneticBlockPath_l1_tendsto N hN hNlim group k hk mag hs hmag hc h
    (fun r => cavityStrictUniformField_height_le rho lam hrho hsum hK hlam (base r) (depth r) (Fin.last (depth r)))
  have hab' : Tendsto (fun r => ∫ t, |b r t-a r t| ∂pathMeasure) atTop (𝓝 0) := by
    simpa only [abs_sub_comm] using hab
  have hb : Tendsto (fun r => ∫ t, |b r t-p t| ∂pathMeasure) atTop (𝓝 0) := by
    apply cavity_magnetic_diagonal_self_consistency rho lam hrho hsum hK hlam N depth hN
      (fun r j => mag r (group r j)) base p hq
    intro Φ
    have hd := overlap_weighted_test_l1_transport (fun r => cavityStrictUniformPath (base r) (depth r)) b a hab' Φ
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
