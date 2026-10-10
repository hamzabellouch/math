import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupAverage
import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockPathConvergence

namespace OAI

/-! Uniform block replacement turns constrained self-consistency into
the weighted magnetic self-consistency used by the entropy supremum. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_group_l1_of_block_consistency {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a) (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ r a, (spinGroupSize (group r) a : ℝ) = N r * γ a)
    {s H : ℝ} (hs : s < 1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ) = spinGroupSize (group r) a * ((1+mag a)/2))
    (h : ℕ → FieldStep) (hH : ∀ r, (h r).height (Fin.last (h r).depth) ≤ H)
    (p : OverlapPath)
    (hself : Tendsto (fun r => ∫ t, |restrictedBlockOverlapPath (hN r)
      (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
      (h r) t-p t| ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun r => ∫ t, |magneticGroupPath γ mag hγ hγsum (h r) t-p t| ∂pathMeasure)
      atTop (𝓝 0) := by
  let a := fun r => restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
    (spinGroupSlice_nonempty (group r) (k r) (hk r)) (h r)
  let b := fun r => magneticGroupPath γ mag hγ hγsum (h r)
  have hab := magneticBlockPath_l1_tendsto N hN hNlim group k hk (fun _ => mag) hs
    (fun _ => hmag) hc h hH
  have he r : magneticBlockPath (hN r) (h r) (fun j => mag (group r j)) = b r :=
    magneticGroupPath_eq_block (hN r) (group r) γ mag hγ hγsum (hcount r) (h r)
  simp_rw [he] at hab
  have hz : Tendsto (fun r => (∫ t, |a r t-b r t| ∂pathMeasure)+
      ∫ t, |a r t-p t| ∂pathMeasure) atTop (𝓝 0) := by
    simpa only [add_zero] using hab.add hself
  apply squeeze_zero (fun r => integral_nonneg (fun t => abs_nonneg _)) (fun r => ?_) hz
  calc
    (∫ t, |b r t-p t| ∂pathMeasure) ≤
        ∫ t, (|a r t-b r t|+|a r t-p t|) ∂pathMeasure := by
      apply integral_mono ((b r).integrable.sub p.integrable).abs
        (((a r).integrable.sub (b r).integrable).abs.add (((a r).integrable.sub p.integrable).abs))
      intro t
      change |b r t-p t| ≤ |a r t-b r t|+|a r t-p t|
      simpa only [abs_sub_comm (b r t) (a r t)] using abs_sub_le (b r t) (a r t) (p t)
    _ = _ := integral_add ((a r).integrable.sub (b r).integrable).abs
      ((a r).integrable.sub p.integrable).abs

end InvariantIsing

end

end OAI
