import OAI.Probability.InvariantIsing.Magnetic.MagneticThresholdDiagonal
import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockTrialLower

namespace OAI

/-! Weak tests on growing physical blocks yield the magnetic variational trial lower bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem magnetic_trial_barrier {m : ℕ}
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ r a, (spinGroupSize (group r) a : ℝ)=N r*γ a)
    {s : ℝ} (hs : s < 1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ)=spinGroupSize (group r) a*((1+mag a)/2))
    (base : ℕ → OverlapPath)
    (htest : ∀ r (Φ : ℝ →ᵇ ℝ), Tendsto (fun j => ∫ t, Φ (cavityStrictUniformPath (base r) j t)*
        (restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
          (spinGroupSlice_nonempty (group r) (k r) (hk r))
          (cavityStrictUniformField ρ lam hρ hsum (base r) j) t-
          cavityStrictUniformPath (base r) j t) ∂pathMeasure) atTop (𝓝 0))
    (L : ℝ)
    (hupper : ∀ r, ∀ ε > 0, ∀ᶠ j in atTop,
      constrainedBlockValue (spinGroupSlice (group r) (k r))
          (cavityStrictUniformField ρ lam hρ hsum (base r) j)+
        fieldPairing (cavityStrictUniformPath (base r) j)
          (cavityStrictUniformField ρ lam hρ hsum (base r) j)/2+
        spectralFunctional (finiteR ρ lam hρ hsum) (cavityStrictUniformPath (base r) j) ≤ L+ε) :
    (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal ≤ L := by
  let T := fun r j => constrainedBlockValue (spinGroupSlice (group r) (k r))
      (cavityStrictUniformField ρ lam hρ hsum (base r) j)+
    fieldPairing (cavityStrictUniformPath (base r) j)
      (cavityStrictUniformField ρ lam hρ hsum (base r) j)/2+
    spectralFunctional (finiteR ρ lam hρ hsum) (cavityStrictUniformPath (base r) j)
  have hup r : ∃ b : ℕ, ∀ j ≥ b, T r j ≤ L+1/((r : ℝ)+1) := by
    exact eventually_atTop.mp (hupper r _ (by positivity))
  choose threshold hthreshold using hup
  obtain ⟨d,φ,p,hd,hφ,hq,hself⟩ := exists_magnetic_consistent_diagonal_above
    ρ lam hρ hsum hK hlam N hN hNlim group k hk (fun _ => mag) hs
      (fun _ => hmag) hc threshold base htest
  have hlower := magnetic_block_trial_eventually_lower ρ lam hρ hsum
    (fun r => N (φ r)) (fun r => hN (φ r)) (hNlim.comp hφ.tendsto_atTop)
    (fun r => group (φ r)) (fun r => k (φ r)) (fun r => hk (φ r)) γ mag hγ hγsum
    (fun r => hcount (φ r)) hs hmag (fun r => hc (φ r))
    (fun r => cavityStrictUniformField ρ lam hρ hsum (base (φ r)) (d (φ r)))
    (fun r => cavityStrictUniformField_height_le ρ lam hρ hsum hK hlam
      (base (φ r)) (d (φ r)) (Fin.last (d (φ r)))) p
    (fun r => cavityStrictUniformPath (base (φ r)) (d (φ r))) hself hq
  have herr : Tendsto (fun r => 1/((φ r : ℝ)+1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r,hr,he⟩ := ((hlower (ε/2) (half_pos hε)).and
    (herr.eventually (Iio_mem_nhds (half_pos hε)))).exists
  have hb := hthreshold (φ r) (d (φ r)) (hd (φ r))
  change (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal-ε/2 ≤
    T (φ r) (d (φ r)) at hr
  linarith

end InvariantIsing

end

end OAI
