import OAI.Analysis.KadisonKastler.StateOrbitSingleton
import OAI.Analysis.KadisonKastler.StateBicentralizerTests
import OAI.Analysis.KadisonKastler.StrongReferenceTests

namespace OAI

/-! # A singleton asymptotic orbit hull gives a bicentralizer element

The unitary estimates extend from the reference vector to every ambient
vector through the dense commutant orbit and uniform operator bounds.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance orbitBicentralizerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem singleton_stateOrbitCore_stateBicentralizer_of_commutant_cyclic
    (ξ : H) (hcyc : DenseRange (algebraVectorMap M.commutant ξ)) (a : Algebra M)
    (hcore : stateOrbitCore ξ a={ContinuousLinearMapWOT.ofCLM a.val}) :
    stateBicentralizerMember ξ a := by
  apply (stateBicentralizerMember_iff_unitary_tests ξ a).mpr
  intro u hu η
  let T (n : ℕ) : Algebra M := a*(u n).val-(u n).val*a
  have htξ : Tendsto (fun n => (T n).val ξ) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := singleton_stateOrbitCore_unitary_control ξ a hcore ε hε
    filter_upwards [hu.eventually (gt_mem_nhds hδ)] with n hn
    have h := hd (u n) hn.le
    change ‖(u n).val.val (a.val ξ)-a.val ((u n).val.val ξ)‖ < ε at h
    change dist (a.val ((u n).val.val ξ)-(u n).val.val (a.val ξ)) 0 < ε
    simpa only [dist_zero_right,norm_sub_rev] using h
  have ht : ∀ n, ‖T n‖ ≤ 2*‖a‖ := by
    intro n
    have hunit := norm_unitary_le_one (u n)
    calc
      _ ≤ ‖a*(u n).val‖+‖(u n).val*a‖ := norm_sub_le _ _
      _ ≤ ‖a‖*‖(u n).val‖+‖(u n).val‖*‖a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 2*‖a‖ := by nlinarith only [hunit,norm_nonneg a]
  exact algebra_strong_tendsto_of_reference ξ
    hcyc T (2*‖a‖)
      (by positivity) ht htξ η

theorem singleton_stateOrbitCore_stateBicentralizer
    (ξ : H) (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M)
    (hcore : stateOrbitCore ξ a={ContinuousLinearMapWOT.ofCLM a.val}) :
    stateBicentralizerMember ξ a :=
  singleton_stateOrbitCore_stateBicentralizer_of_commutant_cyclic ξ
    (commutant_cyclic_of_separating_reference ξ hsep) a hcore

theorem singleton_stateOrbitCore_bicentralizer
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (a : Algebra M)
    (hcore : stateOrbitCore ξ a={ContinuousLinearMapWOT.ofCLM a.val}) :
    vectorBicentralizerMember J ξ a := by
  apply (vectorBicentralizerMember_iff_state_sequences J hJ hright hleft ξ hξ hcyc hpos a).mpr
  exact singleton_stateOrbitCore_stateBicentralizer_of_commutant_cyclic ξ
    (commutant_cyclic_of_fixed_conjugation J hright ξ hξ hcyc) a hcore

end

end KadisonKastler

end OAI
