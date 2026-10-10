import OAI.Analysis.IrrationalRotation.Model.ProductScales
import OAI.Analysis.IrrationalRotation.Model.PhaseBlocks
import OAI.Analysis.IrrationalRotation.Product.ProductTailScaleCover

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem exists_phase_tail_thresholds (θ : ℕ → ℝ) (j : ℕ)
    (hsmall : ∀ s, j < s → ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ s, j ≤ s → ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ)
    (k : ℤ) (hk : p.N j / 4 ≤ |(k : ℝ)|) :
    ∃ (s : ℕ) (w : ℝ) (I : Finset ℕ),
      j ≤ s ∧ (w = p.b s ∨ (j < s ∧ w = p.a s)) ∧
      w ∈ Set.Icc (1 / (p.m s : ℝ)) (1 / 4) ∧
      I ⊆ ProductPhases.consecutiveBlock p.m s ∧ (p.m s : ℝ) / 20 ≤ I.card ∧
      (∀ i ∈ I, 1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc w (1 - w)) ∧
      p.L j ≤ (p.m s : ℝ) * CouplingMarginalBounds.rho
        (ProductScaleData.kappa s) (p.m s) w ∧ p.L j ≤ p.C s := by
  have hcard (s : ℕ) : (ProductPhases.consecutiveBlock p.m s).card = p.m s := by
    simp [ProductPhases.consecutiveBlock]
  have hgrowth (s : ℕ) : 2 ^ s ≤ p.m s := by
    have h := hp.m_ge_pow s
    rw [pow_succ] at h
    have : 0 < 2 ^ s := by positivity
    omega
  have hG (s : ℕ) : (1 : ℝ) ≤ p.G s ∧ 4 * (p.G s : ℝ) ≤ p.m s := by
    constructor
    · exact_mod_cast hp.G_pos s
    · exact_mod_cast hp.m_ge_G s
  have hC (s : ℕ) : p.L s ≤ p.C s := by
    rw [hp.C_eq s]
    exact le_max_left _ _
  have h := ProductPhases.exists_tail_thresholds
    (ProductPhases.consecutiveBlock p.m) (fun s => (p.K s : ℝ))
    (fun s => (p.G s : ℝ)) ProductScaleData.kappa p.L p.C θ j
    (by simpa only [hcard] using fun s (_ : j ≤ s) => hp.m_ge_100 s)
    (by simpa only [hcard] using fun s (_ : j ≤ s) => hgrowth s)
    (by simpa only [hcard] using fun s (_ : j ≤ s) => hG s)
    (by simpa only [hcard, TailScaleCover.upperHorizon] using
      fun s (_ : j ≤ s) => hp.next_gap s)
    (fun s hs => hp.L_monotone hs)
    (fun s _ => hC s)
    (by simpa only [hcard] using fun s (_ : j ≤ s) => hp.m_attenuation s)
    (fun s _ => hp.gain_attenuation s)
    hsmall
    (by simpa only [hcard, ProductScaleData.N] using hlarge)
    k (by simpa only [hcard, ProductScaleData.N] using hk)
  simpa only [hcard, ProductScaleData.a, ProductScaleData.b] using h

theorem eventually_phase_tail_thresholds (θ : ℕ → ℝ)
    (hsmall : ∀ s, ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ᶠ s in atTop, ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ) :
    ∀ᶠ j in atTop, ∀ k : ℤ, p.N j / 4 ≤ |(k : ℝ)| →
      ∃ (s : ℕ) (w : ℝ) (I : Finset ℕ),
        j ≤ s ∧ (w = p.b s ∨ (j < s ∧ w = p.a s)) ∧
        w ∈ Set.Icc (1 / (p.m s : ℝ)) (1 / 4) ∧
        I ⊆ ProductPhases.consecutiveBlock p.m s ∧ (p.m s : ℝ) / 20 ≤ I.card ∧
        (∀ i ∈ I, 1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc w (1 - w)) ∧
        p.L j ≤ (p.m s : ℝ) * CouplingMarginalBounds.rho
          (ProductScaleData.kappa s) (p.m s) w ∧ p.L j ≤ p.C s := by
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hlarge
  apply eventually_atTop.mpr
  refine ⟨j₀, ?_⟩
  intro j hj k hk
  exact hp.exists_phase_tail_thresholds θ j (fun s _ => hsmall s)
    (fun s hs => hj₀ s (hj.trans hs)) k hk

end Invariant233.ProductScaleLaws

end

end OAI
