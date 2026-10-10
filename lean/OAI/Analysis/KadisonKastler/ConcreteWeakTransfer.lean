import OAI.Analysis.KadisonKastler.ConcreteTraceTransfer

namespace OAI

/-! # Weak tracial transfer along an ultrafilter

Weak compactness and the concrete finite-vector trace formula identify
operator ultralimits from their tracial pairings. No Radon–Nikodym or
trace-dual density hypothesis is added.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- On a bounded family, convergence of all tracial pairings determines
the weak operator ultralimit in the original concrete representation. -/
theorem FiniteVectorTrace.weakOperator_ultralimit
    {τ : FaithfulTracialState (Algebra M)} (hτ : FiniteVectorTrace τ)
    {J : Type*} (ω : Ultrafilter J) (x : J → Algebra M) (a : Algebra M)
    {C : ℝ} (hC : 0 ≤ C) (hx : ∀ j, ‖x j‖ ≤ C)
    (htrace : ∀ b : Algebra M,
      Tendsto (fun j => τ.toLinearMap (b * x j)) (ω : Filter J)
        (𝓝 (τ.toLinearMap (b * a)))) :
    ∀ ξ η : H, Tendsto (fun j => inner ℂ η ((x j : H →L[ℂ] H) ξ))
      (ω : Filter J) (𝓝 (inner ℂ η ((a : H →L[ℂ] H) ξ))) := by
  obtain ⟨T, _, hT⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω
    (fun j => (x j : H →L[ℂ] H)) C hC hx
  have hmem : T ∈ M := Generator.Tracial.weak_operator_limit_mem M x T hT
  let t : Algebra M := ⟨T, hmem⟩
  have hpair (b : Algebra M) : τ.toLinearMap (b * t) = τ.toLinearMap (b * a) := by
    apply tendsto_nhds_unique _ (htrace b)
    apply hτ.tendsto
    intro ξ η
    have h := hT ξ ((b : H →L[ℂ] H).adjoint η)
    simpa only [MulMemClass.coe_mul, mul_apply_eq_comp,
      ContinuousLinearMap.adjoint_inner_left] using h
  have hz : τ.toLinearMap (star (t - a) * (t - a)) = 0 := by
    rw [mul_sub, map_sub, hpair, sub_self]
  have hta : t = a := sub_eq_zero.mp (τ.faithful (t - a) hz)
  intro ξ η
  have h := hT ξ η
  change Tendsto (fun j => inner ℂ η ((x j : H →L[ℂ] H) ξ))
    (ω : Filter J) (𝓝 (inner ℂ η ((t : H →L[ℂ] H) ξ))) at h
  simpa only [hta] using h

end

end KadisonKastler

end OAI
