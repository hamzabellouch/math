import OAI.Analysis.KadisonKastler.VectorBicentralizerTests

namespace OAI

/-! # Uniform local tests for vector bicentralizers

The sequential definition is equivalent to a uniform estimate on the
unit ball at each vector. The forward implication constructs an actual
bounded counterexample sequence; the reverse uses the proved unitary tests.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H) (hξ : J ξ = ξ)

include hJ hright hξ in
theorem vectorBicentralizerMember_iff_local (a : Algebra M) :
    vectorBicentralizerMember J ξ a ↔
      ∀ η : H, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ b : Algebra M, ‖b‖ ≤ 1 → ‖centralVectorDefect J ξ b.val‖ < δ →
          ‖(a*b-b*a).val η‖ < ε := by
  constructor
  · intro ha η ε hε
    by_contra h
    push Not at h
    choose b hb using fun n : ℕ => h (1 / ((n : ℝ)+1)) (by positivity)
    let x : BoundedSequence (Algebra M) :=
      BoundedContinuousFunction.ofNormedAddCommGroupDiscrete b 1 (fun n => (hb n).1)
    have hx : AsymptoticallyCentral J ξ x := by
      apply squeeze_zero (fun _ => norm_nonneg _)
        (fun n => (hb n).2.1.le)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have ht : Tendsto (fun n => ‖(a*b n-b n*a).val η‖) atTop (𝓝 0) := by
      have ht := (ha x hx η).norm
      change Tendsto (fun n => ‖(a*b n-b n*a).val η‖) atTop (𝓝 ‖(0 : H)‖) at ht
      simpa only [norm_zero] using ht
    obtain ⟨n,hn⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
    exact (not_lt_of_ge (hb n).2.2) (hn n le_rfl)
  · intro ha
    let : Nontrivial (centralSequenceAlgebra J hJ hright ξ hξ) := by
      refine ⟨⟨0,1,?_⟩⟩
      intro h
      have he := congrArg (fun z : centralSequenceAlgebra J hJ hright ξ hξ => z.val 0) h
      exact zero_ne_one (he : (0 : Algebra M) = 1)
    apply (vectorBicentralizerMember_iff_unitary J hJ hright ξ hξ a).mpr
    intro u η
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ,hδ,hb⟩ := ha η ε hε
    have hx : Tendsto (fun n => ‖centralVectorDefect J ξ (u.val.val n).val‖)
        atTop (𝓝 0) := u.val.property
    filter_upwards [hx.eventually (gt_mem_nhds hδ)] with n hn
    have hbound : ‖u.val.val n‖ ≤ 1 := by
      calc
        _ ≤ ‖u.val.val‖ := u.val.val.norm_coe_le_norm n
        _ = ‖u.val‖ := rfl
        _ = 1 := CStarRing.norm_coe_unitary u
    simpa only [dist_zero_right] using hb (u.val.val n) hbound hn

end

end KadisonKastler

end OAI
