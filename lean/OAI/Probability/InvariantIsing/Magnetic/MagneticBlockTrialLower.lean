import OAI.Probability.InvariantIsing.Magnetic.MagneticEntropyMaximum
import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupConsistency

namespace OAI

/-! The original constrained block trial attains the magnetic
variational lower bound once its physical overlap is self-consistent. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_block_trial_eventually_lower {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a) (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ r a, (spinGroupSize (group r) a : ℝ) = N r * γ a)
    {s H : ℝ} (hs : s<1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ) = spinGroupSize (group r) a*((1+mag a)/2))
    (h : ℕ → FieldStep) (hH : ∀ r, (h r).height (Fin.last (h r).depth) ≤ H)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hself : Tendsto (fun r => ∫ t, |restrictedBlockOverlapPath (hN r)
      (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
      (h r) t-p t| ∂pathMeasure) atTop (𝓝 0))
    (hq : Tendsto (fun r => ∫ t, |q r t-p t| ∂pathMeasure) atTop (𝓝 0)) :
    ∀ ε>0, ∀ᶠ r in atTop,
      (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal-ε ≤
        constrainedBlockValue (spinGroupSlice (group r) (k r)) (h r)+
          fieldPairing (q r) (h r)/2+spectralFunctional (finiteR ρ eig hρ hsum) (q r) := by
  have hgroup := magnetic_group_l1_of_block_consistency N hN hNlim group k hk γ mag
    hγ hγsum hcount hs hmag hc h hH p hself
  have hlower := magnetic_entropy_trial_eventually_lower ρ eig hρ hsum γ mag hγ hγsum
    (fun a => (hmag a).trans_lt hs) p q h hH hgroup hq
  have hgap := magneticBlockGap_tendsto N hN hNlim group k hk (fun _ => mag) hs
    (fun _ => hmag) hc h hH
  have he r : (N r : ℝ)⁻¹*(∑ j, constrainedFieldValue (h r) (mag (group r j))) =
      magneticGroupValue γ mag (h r) :=
    magneticGroupValue_eq_block (hN r) (group r) γ mag (hcount r) (h r)
  simp_rw [he] at hgap
  intro ε hε
  filter_upwards [hlower (ε/2) (half_pos hε),
    hgap.eventually (Iio_mem_nhds (half_pos hε))] with r hr hgapr
  linarith

end InvariantIsing

end

end OAI
