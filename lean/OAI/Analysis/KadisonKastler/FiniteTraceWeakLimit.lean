import OAI.Analysis.KadisonKastler.ContractiveWeakLimit
import OAI.Analysis.KadisonKastler.ConcreteTraceTransfer

namespace OAI

/-! # Ambient projections detected by a finite normal trace

The trace need only have a finite vector-functional expression. Uniform
contractivity and convergence in its two-norm suffice on the original space.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M Q : VonNeumannAlgebra H}

/-- The finite-vector trace replaces a separating trace vector in the weak-limit construction. -/
theorem isInjective_of_finiteTrace_approximations
    (hQM : Q ≤ M) (τ : FaithfulTracialState (Algebra M)) (hτ : FiniteVectorTrace τ)
    (F : ℕ → (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hF : ∀ n, ‖F n‖ ≤ 1) (hmem : ∀ n T, F n T ∈ Q)
    (hfix : ∀ a : Algebra Q, Tendsto
      (fun n => traceTwoNorm τ
        ((⟨F n a.val,hQM (hmem n a.val)⟩ : Algebra M) - coordinateInclusion hQM a))
      atTop (𝓝 0)) : IsInjective Q := by
  have hstrong (a : Algebra Q) (z : H) :
      Tendsto (fun n => F n a.val z) atTop (𝓝 (a.val z)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := hτ.strongContinuous z (2 * ‖a‖) (by positivity) ε hε
    obtain ⟨k,hk⟩ := (Metric.tendsto_atTop.mp (hfix a)) δ hδ
    refine ⟨k,fun n hn => ?_⟩
    have hnorm : ‖(⟨F n a.val,hQM (hmem n a.val)⟩ : Algebra M) -
        coordinateInclusion hQM a‖ ≤ 2 * ‖a‖ := by
      change ‖F n a.val - a.val‖ ≤ 2 * ‖a.val‖
      have hb := (F n).le_of_opNorm_le (hF n) a.val
      rw [one_mul] at hb
      exact (norm_sub_le _ _).trans (by linarith)
    have hsmall := hk n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (traceTwoNorm_nonneg τ _)] at hsmall
    have hv := hd _ hnorm hsmall
    change ‖F n a.val z - a.val z‖ < ε at hv
    simpa only [dist_eq_norm] using hv
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨E,hE,ht⟩ := exists_contractive_weak_ultralimit ω F hF
  refine ⟨E,hE,?_,?_⟩
  · intro T
    exact weak_operator_limit_mem Q (fun n => ⟨F n T,hmem n T⟩) (E T) (ht T)
  · intro T hT
    ext z
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht T z y)
    exact ((continuous_const.inner continuous_id).tendsto _).comp
      ((hstrong ⟨T,hT⟩ z).mono_left (Ultrafilter.of_le atTop))

end

end KadisonKastler

end OAI
