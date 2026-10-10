import OAI.Analysis.KadisonKastler.UnitaryStateDefect
import OAI.Analysis.KadisonKastler.VectorBicentralizerTests

namespace OAI

/-! # State and vector unitary tests for the bicentralizer

The constructed two-sided norm estimates identify the two sequential
centrality tests. The resulting characterization retains all ambient
vector tests in the definition of the bicentralizer.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance stateUnitaryCentralizerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
  (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
  (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))

include hJ hright hleft hξ hcyc hpos in
theorem unitary_centrality_iff_state_commutator (u : ℕ → unitary (Algebra M)) :
    Tendsto (fun n => ‖centralVectorDefect J ξ (u n).val.val‖) atTop (𝓝 0) ↔
      Tendsto (fun n => ‖vectorStateCommutator ξ (u n).val‖) atTop (𝓝 0) := by
  constructor
  · intro h
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => vectorStateCommutator_norm_le J hJ hright ξ hξ (u n).val)
    simpa only [mul_zero] using h.const_mul (2*‖ξ‖)
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [h.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with n hn
    have hb := centralVectorDefect_unitary_sq_le_stateCommutator
      J hJ hright hleft ξ hξ hcyc hpos (u n)
    have hd : ‖centralVectorDefect J ξ (u n).val.val‖ < ε := by
      nlinarith [norm_nonneg (centralVectorDefect J ξ (u n).val.val)]
    simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hd

include hJ hright hleft hξ hcyc hpos in
theorem vectorBicentralizerMember_iff_state_unitary_tests (a : Algebra M) :
    vectorBicentralizerMember J ξ a ↔
      ∀ u : ℕ → unitary (Algebra M),
        Tendsto (fun n => ‖vectorStateCommutator ξ (u n).val‖) atTop (𝓝 0) →
        ∀ η : H, Tendsto (fun n => (a*(u n).val-(u n).val*a).val η) atTop (𝓝 0) := by
  constructor
  · intro ha u hu η
    let x : BoundedSequence (Algebra M) :=
      BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => (u n).val) 1
        (fun n => norm_unitary_le_one (u n))
    have hx : AsymptoticallyCentral J ξ x :=
      (unitary_centrality_iff_state_commutator J hJ hright hleft ξ hξ hcyc hpos u).mpr hu
    exact ha x hx η
  · intro ha
    apply (vectorBicentralizerMember_iff_unitary J hJ hright ξ hξ a).mpr
    intro u η
    let v (n : ℕ) : unitary (Algebra M) := ⟨u.val.val n,by
      constructor
      · exact congrArg (fun x : centralSequenceAlgebra J hJ hright ξ hξ => x.val n)
          u.property.1
      · exact congrArg (fun x : centralSequenceAlgebra J hJ hright ξ hξ => x.val n)
          u.property.2⟩
    have hv : Tendsto (fun n => ‖vectorStateCommutator ξ (v n).val‖) atTop (𝓝 0) :=
      (unitary_centrality_iff_state_commutator J hJ hright hleft ξ hξ hcyc hpos v).mp
        u.val.property
    exact ha v hv η

end

end KadisonKastler

end OAI
