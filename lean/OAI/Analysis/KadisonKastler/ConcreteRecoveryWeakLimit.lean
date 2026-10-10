import OAI.Analysis.KadisonKastler.RecoveryWeakLimit
import OAI.Analysis.KadisonKastler.ConcreteHaarRecovery

namespace OAI

/-! # Scalar weak recovery with the actual positive lower bound -/

namespace KadisonKastler

open Filter

noncomputable section

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {P : VonNeumannAlgebra K}
variable {τ : FaithfulTracialState (Algebra M)} {σ : FaithfulTracialState (Algebra P)}
variable {ω : Ultrafilter ℕ}

/-- Combining the constructed expectation and spectral recovery gives
both pieces needed by the randomized-row argument. The recovered scalar
has real part at least one half and is the weak limit of the coordinate
recovery average. -/
theorem TraceQuotientMap.exists_recovery_weak_scalar
    (D : TraceQuotientMap τ σ ω)
    (hτ : FiniteVectorTrace τ) (hσ : FiniteVectorTrace σ)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → Algebra M) (v : ι → unitary (BoundedSequence (Algebra M)))
    (u : ι → unitary (Algebra P))
    (hu : ∀ i, D.quotient (v i : BoundedSequence (Algebra M)) = (u i : Algebra P))
    (hp : ∀ i, IsStarProjection (p i))
    (hfree : ∀ i, FreeHaarMoments σ D.constant.range (u i))
    {n N : ℕ} (hn : 2 ≤ n)
    (hptrace : ∀ i, τ.toLinearMap (p i) = (((n : ℝ)⁻¹ : ℝ) : ℂ))
    (hpavg : finiteAverage p = (((n : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Algebra M))
    (hsize : 100 * (n : ℝ) * (100 * Real.pi) ^ 3 ≤ N) :
    ∃ c : ℂ, 1 / 2 ≤ c.re ∧
      WeakOperatorConverges (ω : Filter ℕ)
        (fun j => ((finiteAverage (fun i => recoveryObservable n N
          (boundedSequenceConst (p i)) (v i))) j : H →L[ℂ] H))
        (c • ContinuousLinearMap.id ℂ H) := by
  have hn0 : 0 < n := by omega
  have hnℝ : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have ht0 : ((((n : ℝ)⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (inv_ne_zero (ne_of_gt hnℝ))
  have ht1 : ((((n : ℝ)⁻¹ : ℝ) : ℂ)) ≠ 1 := by
    intro h
    have hreal : (n : ℝ)⁻¹ = 1 := by exact_mod_cast h
    have hn1 : (n : ℝ) = 1 := inv_eq_one.mp hreal
    have : n = 1 := by exact_mod_cast hn1
    omega
  let i₀ : ι := Classical.arbitrary ι
  let c := σ.toLinearMap (recoveryObservable n N (D.constant (p i₀)) (u i₀))
  refine ⟨c, ?_, D.recovery_average_weak_limit hτ p v u hu hp hfree hptrace ht0 ht1 hpavg hn0 N i₀⟩
  apply concrete_haar_recovery_at_least_half σ hσ (u i₀) (hfree i₀) hn0 hsize
  · exact (hp i₀).map D.constant
  · exact ⟨p i₀, rfl⟩
  · rw [D.trace_constant, hptrace]

end

end KadisonKastler

end OAI
